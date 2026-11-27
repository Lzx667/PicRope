using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using System.Web.Script.Serialization;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Imaging;

namespace ScreenLine
{
    internal sealed class SavedState
    {
        public bool CollectClipboard { get; set; }
        public bool CollectTextClipboard { get; set; }
        public bool AutoHang { get; set; }
        // 隔天下绳：新的一天开始后，之前上绳的图片自动取下到篮子。旧配置没有这一项，读取时保持默认开启。
        public bool AutoTakeDown { get; set; }
        public bool HoverPreview { get; set; }
        public bool RevealOnTopPush { get; set; }
        public bool RevealOnTopHover { get; set; }
        public bool ToggleShortcut { get; set; }
        public string Theme { get; set; }
        public string DisplayDevice { get; set; }
        public string LastUpdateNotification { get; set; }
        public uint CaptureModifiers { get; set; }
        public uint CaptureKey { get; set; }
        public uint ToggleModifiers { get; set; }
        public uint ToggleKey { get; set; }
        public List<string> Images { get; set; }
        public List<string> Collection { get; set; }
        // 绳上各图片的上绳时间（UTC），路径为键，与 Images 一起保存。
        public Dictionary<string, DateTime> Hung { get; set; }
        public List<TextItem> Texts { get; set; }

        public SavedState() { Images = new List<string>(); Collection = new List<string>(); Hung = new Dictionary<string, DateTime>(); Texts = new List<TextItem>(); Theme = "classic"; AutoHang = true; AutoTakeDown = true; HoverPreview = true; RevealOnTopPush = true; RevealOnTopHover = false; ToggleShortcut = true; CaptureModifiers = 3; CaptureKey = (uint)'S'; ToggleModifiers = 3; ToggleKey = (uint)'T'; }
    }

    internal sealed class TopPushDetector
    {
        public const int DefaultThreshold = 20;
        public const int DefaultPauseMs = 45;
        public const int DefaultDoubleWindowMs = 600;
        public const int DefaultCooldownMs = 450;
        readonly int threshold;
        readonly TimeSpan pause;
        readonly TimeSpan doubleWindow;
        readonly TimeSpan cooldown;
        bool awaitingGap;
        int stroke;
        int horizontal;
        DateTime lastUp = DateTime.MinValue;
        DateTime firstBumpAt = DateTime.MinValue;
        DateTime cooldownUntil = DateTime.MinValue;

        public TopPushDetector(int threshold = DefaultThreshold, int pauseMs = DefaultPauseMs, int doubleWindowMs = DefaultDoubleWindowMs, int cooldownMs = DefaultCooldownMs)
        {
            this.threshold = threshold;
            pause = TimeSpan.FromMilliseconds(pauseMs);
            doubleWindow = TimeSpan.FromMilliseconds(doubleWindowMs);
            cooldown = TimeSpan.FromMilliseconds(cooldownMs);
        }

        public void Reset()
        {
            awaitingGap = false;
            stroke = 0;
            horizontal = 0;
            lastUp = DateTime.MinValue;
            firstBumpAt = DateTime.MinValue;
        }

        public bool Feed(bool atTop, bool nearTop, int dx, int dy, DateTime now)
        {
            if (!nearTop)
            {
                Reset();
                return false;
            }
            if (now < cooldownUntil)
            {
                awaitingGap = false;
                stroke = 0;
                horizontal = 0;
                firstBumpAt = DateTime.MinValue;
                return false;
            }
            // 两下上推之间允许自然回拉离开顶边（仍在顶部区域内），直接视为分隔两下。
            if (!atTop)
            {
                stroke = 0;
                horizontal = 0;
                if (firstBumpAt != DateTime.MinValue) awaitingGap = false;
                return false;
            }
            if (firstBumpAt != DateTime.MinValue && now - firstBumpAt > doubleWindow)
            {
                firstBumpAt = DateTime.MinValue;
                awaitingGap = false;
            }
            if (dy > 0)
            {
                stroke = 0;
                horizontal = 0;
                if (firstBumpAt != DateTime.MinValue) awaitingGap = false;
                return false;
            }
            if (dy < 0)
            {
                if (lastUp != DateTime.MinValue && now - lastUp >= pause)
                {
                    stroke = 0;
                    horizontal = 0;
                    if (firstBumpAt != DateTime.MinValue) awaitingGap = false;
                }
                lastUp = now;
                // 第一下的连续惯性包全部忽略，直到出现停顿或回拉才开始计第二下。
                if (awaitingGap)
                {
                    firstBumpAt = now;
                    return false;
                }
                stroke += -dy;
                horizontal += Math.Abs(dx);
                if (stroke >= threshold && stroke >= horizontal * 0.65)
                {
                    if (firstBumpAt == DateTime.MinValue)
                    {
                        firstBumpAt = now;
                        awaitingGap = true;
                        stroke = 0;
                        horizontal = 0;
                        return false;
                    }
                    Reset();
                    cooldownUntil = now + cooldown;
                    return true;
                }
            }
            else if (dx != 0 && stroke > 0)
            {
                horizontal += Math.Abs(dx);
                if (horizontal > threshold * 3)
                {
                    stroke = 0;
                    horizontal = 0;
                }
            }
            return false;
        }
    }

    internal static class ShortcutRules
    {
        public static bool IsValid(uint modifiers, uint key)
        {
            return modifiers != 0 && (modifiers & ~15u) == 0 && key >= 0x20 && key <= 0xFE
                && key != 0x5B && key != 0x5C && (key < 0xA0 || key > 0xA5);
        }
    }

    internal sealed class StateStore
    {
        public static string DefaultRoot { get { return Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "data"); } }
        public readonly string Root;
        public readonly string Inbox;
        public readonly SavedState State;
        readonly JavaScriptSerializer serializer = new JavaScriptSerializer { MaxJsonLength = int.MaxValue };
        readonly string file;

        public StateStore(string root)
        {
            Root = Path.GetFullPath(root);
            Inbox = Path.Combine(Root, "Captures");
            file = Path.Combine(Root, "state.json");
            State = new SavedState();
            if (!File.Exists(file)) return;
            try
            {
                string raw = File.ReadAllText(file, Encoding.UTF8);
                State = serializer.Deserialize<SavedState>(raw) ?? new SavedState();
                // 旧版配置文件没有 RevealOnTopPush 字段，保持其原有的悬停/快捷键展开方式。
                if (raw.IndexOf("\"RevealOnTopPush\"", StringComparison.OrdinalIgnoreCase) < 0)
                {
                    State.RevealOnTopPush = false;
                    if (raw.IndexOf("\"RevealOnTopHover\"", StringComparison.OrdinalIgnoreCase) < 0)
                        State.RevealOnTopHover = true;
                }
                else if (State.RevealOnTopPush && State.RevealOnTopHover)
                {
                    State.RevealOnTopHover = false;
                }
                if (State.Images == null) State.Images = new List<string>();
                if (State.Collection == null) State.Collection = new List<string>();
                if (State.Hung == null) State.Hung = new Dictionary<string, DateTime>();
                if (State.Texts == null) State.Texts = new List<TextItem>();
                if (!ShortcutRules.IsValid(State.ToggleModifiers, State.ToggleKey)) { State.ToggleModifiers = 3; State.ToggleKey = (uint)'T'; }
            }
            catch (ArgumentException ex) { Log(ex); }
            catch (InvalidOperationException ex) { Log(ex); }
            catch (IOException ex) { Log(ex); }
        }

        public void Save()
        {
            Directory.CreateDirectory(Root);
            string temporary = file + ".tmp";
            File.WriteAllText(temporary, serializer.Serialize(State), new UTF8Encoding(false));
            FileRules.Commit(temporary, file);
        }

        public void Log(Exception error)
        {
            Directory.CreateDirectory(Root);
            File.AppendAllText(Path.Combine(Root, "error.log"), DateTime.Now.ToString("s") + " " + error + Environment.NewLine);
        }
    }

    internal sealed class TextItem : System.ComponentModel.INotifyPropertyChanged
    {
        public string Id { get; set; }
        public string Content { get; set; }
        public DateTime CreatedUtc { get; set; }
        bool marked;
        [System.Web.Script.Serialization.ScriptIgnore]
        public bool IsMarked
        {
            get { return marked; }
            set { if (marked == value) return; marked = value; if (PropertyChanged != null) PropertyChanged(this, new System.ComponentModel.PropertyChangedEventArgs("IsMarked")); }
        }
        public event System.ComponentModel.PropertyChangedEventHandler PropertyChanged;
    }

    internal sealed class TextCollection
    {
        public readonly StateStore Store;
        public List<TextItem> Items { get { return Store.State.Texts; } }
        public event Action Changed;

        public TextCollection(StateStore store) { Store = store; }

        public bool CollectClipboard
        {
            get { return Store.State.CollectTextClipboard; }
            set
            {
                bool previous = CollectClipboard;
                if (previous == value) return;
                Store.State.CollectTextClipboard = value;
                try { Store.Save(); }
                catch { Store.State.CollectTextClipboard = previous; throw; }
                if (Changed != null) Changed();
            }
        }

        public TextItem Add(string content)
        {
            if (string.IsNullOrWhiteSpace(content)) return null;
            var existing = Items.Find(item => item.Content == content);
            if (existing != null) return existing;
            var added = new TextItem { Id = Guid.NewGuid().ToString("N"), Content = content, CreatedUtc = DateTime.UtcNow };
            Items.Insert(0, added);
            try { Store.Save(); }
            catch { Items.Remove(added); throw; }
            if (Changed != null) Changed();
            return added;
        }

        public void Remove(TextItem item)
        {
            int index = Items.IndexOf(item);
            if (index < 0) return;
            Items.RemoveAt(index);
            try { Store.Save(); }
            catch { Items.Insert(index, item); throw; }
            if (Changed != null) Changed();
        }

        public void RemoveMany(IEnumerable<TextItem> selected)
        {
            var ids = new HashSet<string>(selected.Select(item => item.Id));
            var previous = Items.ToArray();
            if (Items.RemoveAll(item => ids.Contains(item.Id)) == 0) return;
            try { Store.Save(); }
            catch { Items.Clear(); Items.AddRange(previous); throw; }
            if (Changed != null) Changed();
        }
    }

    internal static class FileRules
    {
        static readonly string[] extensions = { ".png", ".jpg", ".jpeg", ".bmp", ".gif", ".tif", ".tiff" };

        public static void Commit(string temporary, string destination)
        {
            for (int attempt = 0; ; attempt++)
            {
                try
                {
                    if (File.Exists(destination)) File.Replace(temporary, destination, null);
                    else File.Move(temporary, destination);
                    return;
                }
                catch (IOException error)
                {
                    int code = error.HResult & 65535;
                    if (attempt == 4 || (code != 32 && code != 33 && code != 1175)) throw;
                    // 索引或杀毒扫描短暂占用时重试，仍以原子替换保护已有文件。
                    System.Threading.Thread.Sleep(30);
                }
            }
        }

        public static bool IsImage(string path)
        {
            return extensions.Contains(Path.GetExtension(path), StringComparer.OrdinalIgnoreCase);
        }

        public static bool IsInside(string path, string directory)
        {
            string prefix = Path.GetFullPath(directory).TrimEnd(Path.DirectorySeparatorChar) + Path.DirectorySeparatorChar;
            return Path.GetFullPath(path).StartsWith(prefix, StringComparison.OrdinalIgnoreCase);
        }

        public static bool SameFile(string a, string b)
        {
            return string.Equals(Path.GetFullPath(a), Path.GetFullPath(b), StringComparison.OrdinalIgnoreCase);
        }
    }

    internal static class ClipboardRules
    {
        public const string OwnFormat = "PicRope.OwnClipboard";
        internal static readonly KeyValuePair<string, string>[] EncodedFormats = {
            new KeyValuePair<string, string>("PNG", ".png"), new KeyValuePair<string, string>("image/png", ".png"),
            new KeyValuePair<string, string>("image/jpeg", ".jpg"), new KeyValuePair<string, string>("image/jpg", ".jpg"), new KeyValuePair<string, string>("image/jpe", ".jpg"),
            new KeyValuePair<string, string>("image/bmp", ".bmp"), new KeyValuePair<string, string>("image/gif", ".gif"),
            new KeyValuePair<string, string>("image/tiff", ".tiff"), new KeyValuePair<string, string>("image/tif", ".tiff")
        };
        static readonly string[] excluded = { "HTML Format", "UnicodeText", "Text", "System.String", "FileDrop", "Rich Text Format" };
        static readonly TimeSpan htmlTimeout = TimeSpan.FromMilliseconds(200);

        public static bool IsPlainImage(IEnumerable<string> formats)
        {
            var values = new HashSet<string>(formats, StringComparer.OrdinalIgnoreCase);
            return !values.Overlaps(excluded) && HasImage(values);
        }

        static bool HasImage(HashSet<string> formats)
        {
            return formats.Contains("Bitmap") || formats.Contains("DeviceIndependentBitmap") || formats.Contains("Format17")
                || EncodedFormats.Any(format => formats.Contains(format.Key));
        }

        public static bool IsImage(IDataObject data) { return IsImage(data, null); }

        public static bool IsImage(IDataObject data, string source)
        {
            string imageFile;
            return IsImage(data, source, out imageFile);
        }

        public static bool IsImage(IDataObject data, string source, out string imageFile)
        {
            imageFile = null;
            var formats = new HashSet<string>(data.GetFormats(), StringComparer.OrdinalIgnoreCase);
            if (formats.Contains(OwnFormat)) return false;
            if (IsPlainImage(formats)) return true;
            if (formats.Contains("FileDrop"))
            {
                bool wechat = string.Equals(source, "Weixin", StringComparison.OrdinalIgnoreCase) || string.Equals(source, "WeChat", StringComparison.OrdinalIgnoreCase);
                if (!wechat || !formats.Contains("image/png") || !formats.Contains("DeviceIndependentBitmap")
                    || formats.Contains("HTML Format") || formats.Contains("Rich Text Format") || formats.Contains("UnicodeText") || formats.Contains("Text") || formats.Contains("System.String")) return false;
                var files = data.GetData(DataFormats.FileDrop) as string[];
                if (files == null || files.Length != 1 || !FileRules.IsImage(files[0])) return false;
                imageFile = files[0]; return true;
            }
            if (formats.Contains("Rich Text Format") || !formats.Contains("HTML Format") || !HasImage(formats)) return false;
            string html = data.GetData(DataFormats.Html) as string;
            if (string.IsNullOrEmpty(html) || html.Length > 1024 * 1024) return false;
            const string start = "<!--StartFragment-->", end = "<!--EndFragment-->";
            int first = html.IndexOf(start, StringComparison.OrdinalIgnoreCase), last = html.IndexOf(end, StringComparison.OrdinalIgnoreCase);
            if (first >= 0 || last >= 0)
            {
                if (first < 0 || last < first + start.Length) return false;
                html = html.Substring(first + start.Length, last - first - start.Length);
            }
            else
            {
                int document = html.IndexOf("<html", StringComparison.OrdinalIgnoreCase);
                if (document >= 0) html = html.Substring(document);
            }
            try
            {
                var options = RegexOptions.IgnoreCase | RegexOptions.CultureInvariant;
                html = Regex.Replace(html, @"<!--[\s\S]*?-->", "", options, htmlTimeout);
                const string tail = @"(?:[^'"">]|""[^""]*""|'[^']*')*";
                var images = Regex.Matches(html, @"<\s*img\b" + tail + @">", options, htmlTimeout);
                if (images.Count != 1) return false;
                string text = data.GetData(DataFormats.UnicodeText) as string ?? data.GetData(DataFormats.Text) as string ?? data.GetData("System.String") as string;
                if (!string.IsNullOrWhiteSpace(text))
                {
                    var imageSource = Regex.Match(images[0].Value, @"\ssrc\s*=\s*(?:""(?<url>[^""]*)""|'(?<url>[^']*)'|(?<url>[^\s>]+))", options, htmlTimeout);
                    if (!imageSource.Success || !string.Equals(text.Trim(), WebUtility.HtmlDecode(imageSource.Groups["url"].Value), StringComparison.Ordinal)) return false;
                }
                html = html.Remove(images[0].Index, images[0].Length);
                html = Regex.Replace(html, @"<\s*/?\s*(?:html|body|div|span|p|a|figure|br)\b" + tail + @">", "", options, htmlTimeout);
                return string.IsNullOrWhiteSpace(WebUtility.HtmlDecode(html));
            }
            catch (RegexMatchTimeoutException) { return false; }
        }

    }

    internal sealed class ImageContent
    {
        static readonly LinkedList<ImageContent> cache = new LinkedList<ImageContent>();
        BitmapSource thumbnail;
        string backingPath;
        LinkedListNode<ImageContent> cacheNode;
        internal BitmapSource CachedThumbnail
        {
            get
            {
                if (!System.Threading.Monitor.TryEnter(cache)) return null;
                try { if (thumbnail != null) Touch(); return thumbnail; }
                finally { System.Threading.Monitor.Exit(cache); }
            }
        }
        public BitmapSource Thumbnail
        {
            get
            {
                string path;
                lock (cache)
                {
                    if (thumbnail != null) { Touch(); return thumbnail; }
                    path = backingPath;
                }
                BitmapSource loaded;
                using (var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite | FileShare.Delete))
                    loaded = MakeThumbnail(stream, PixelWidth, PixelHeight);
                lock (cache)
                {
                    if (thumbnail == null) thumbnail = loaded;
                    Touch(); return thumbnail;
                }
            }
        }
        public readonly string Fingerprint;
        public readonly int PixelWidth, PixelHeight;

        ImageContent(BitmapSource thumbnail, string fingerprint, int width, int height)
        {
            this.thumbnail = thumbnail;
            Fingerprint = fingerprint;
            PixelWidth = width;
            PixelHeight = height;
        }

        internal void BindFile(string path)
        {
            lock (cache) { backingPath = path; if (thumbnail != null) Touch(); }
        }

        internal ImageContent ForFile(string path)
        {
            lock (cache)
            {
                var image = backingPath != null && !FileRules.SameFile(backingPath, path)
                    ? new ImageContent(thumbnail, Fingerprint, PixelWidth, PixelHeight) : this;
                image.BindFile(path); return image;
            }
        }

        void Touch()
        {
            if (backingPath == null) return;
            if (cacheNode != null) cache.Remove(cacheNode);
            cacheNode = cache.AddLast(this);
            while (cache.Count > 64)
            {
                var evicted = cache.First.Value; cache.RemoveFirst();
                evicted.cacheNode = null; evicted.thumbnail = null;
            }
        }

        public static ImageContent Read(string path)
        {
            return Read(path, true);
        }

        public static ImageContent Read(string path, bool fingerprint)
        {
            using (var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite | FileShare.Delete))
            {
                if (stream.Length == 0 || stream.Length > 64L * 1024 * 1024) throw new InvalidDataException("Image file size is invalid");
                if (!fingerprint)
                {
                    var frame = BitmapDecoder.Create(stream, BitmapCreateOptions.DelayCreation, BitmapCacheOption.None).Frames[0];
                    if (frame.PixelWidth <= 0 || frame.PixelHeight <= 0 || (long)frame.PixelWidth * frame.PixelHeight > 80000000) throw new InvalidDataException("Image dimensions are invalid");
                    var metadata = new ImageContent(null, null, frame.PixelWidth, frame.PixelHeight); metadata.BindFile(path); return metadata;
                }
                using (var memory = new MemoryStream())
                {
                    stream.CopyTo(memory);
                    var image = Decode(memory.ToArray(), fingerprint); image.BindFile(path); return image;
                }
            }
        }

        public static ImageContent Decode(byte[] bytes)
        {
            return Decode(bytes, true);
        }

        static ImageContent Decode(byte[] bytes, bool fingerprint)
        {
            using (var memory = new MemoryStream(bytes))
            {
                var full = BitmapDecoder.Create(memory, BitmapCreateOptions.DelayCreation, BitmapCacheOption.None).Frames[0];
                if (full.PixelWidth <= 0 || full.PixelHeight <= 0 || (long)full.PixelWidth * full.PixelHeight > 80000000)
                    throw new InvalidDataException("Image dimensions are invalid");
                string hash = fingerprint ? HashPixels(full) : null;
                memory.Position = 0;
                return new ImageContent(MakeThumbnail(memory, full.PixelWidth, full.PixelHeight), hash, full.PixelWidth, full.PixelHeight);
            }
        }

        static BitmapSource MakeThumbnail(Stream stream, int width, int height)
        {
            var image = new BitmapImage(); image.BeginInit(); image.CacheOption = BitmapCacheOption.OnLoad; image.StreamSource = stream;
            if (width >= height) image.DecodePixelWidth = Math.Min(240, width); else image.DecodePixelHeight = Math.Min(240, height);
            image.EndInit();
            var color = new FormatConvertedBitmap(image, PixelFormats.Bgra32, null, 0);
            int stride = color.PixelWidth * 4; byte[] pixels = new byte[stride * color.PixelHeight];
            color.CopyPixels(pixels, stride, 0);
            var detached = BitmapSource.Create(color.PixelWidth, color.PixelHeight, 96, 96, PixelFormats.Bgra32, null, pixels, stride);
            detached.Freeze(); return detached;
        }

        // 原文件已是 PNG 时，直接用文件字节作为剪贴板的 PNG 数据，省去整图重新编码；
        // 透明通道全为零的图仍按不透明图像重新编码。
        public static byte[] ClipboardPng(BitmapDecoder decoder, byte[] file)
        {
            var image = decoder.Frames[0];
            bool reusable = decoder is PngBitmapDecoder && !EmptyAlpha(new FormatConvertedBitmap(image, PixelFormats.Bgra32, null, 0));
            return reusable ? file : EncodeClipboard(image);
        }

        static bool EmptyAlpha(BitmapSource converted)
        {
            int stride = converted.PixelWidth * 4;
            byte[] rows = new byte[stride * Math.Min(32, converted.PixelHeight)];
            for (int y = 0; y < converted.PixelHeight; y += 32)
            {
                int height = Math.Min(32, converted.PixelHeight - y);
                converted.CopyPixels(new Int32Rect(0, y, converted.PixelWidth, height), rows, stride, 0);
                for (int i = 3; i < stride * height; i += 4)
                    if (rows[i] != 0) return false;
            }
            return true;
        }

        public static byte[] EncodeClipboard(BitmapSource image)
        {
            // 部分 Windows 位图的透明通道全为零，截图应按不透明图像保存。
            var converted = new FormatConvertedBitmap(image, PixelFormats.Bgra32, null, 0);
            int stride = converted.PixelWidth * 4;
            if (EmptyAlpha(converted))
            {
                byte[] pixels = new byte[stride * converted.PixelHeight];
                converted.CopyPixels(pixels, stride, 0);
                for (int i = 3; i < pixels.Length; i += 4) pixels[i] = 255;
                image = BitmapSource.Create(converted.PixelWidth, converted.PixelHeight, 96, 96, PixelFormats.Bgra32, null, pixels, stride);
            }
            var encoder = new PngBitmapEncoder();
            encoder.Frames.Add(BitmapFrame.Create(image));
            using (var memory = new MemoryStream()) { encoder.Save(memory); return memory.ToArray(); }
        }

        public static string HashPixels(BitmapSource image)
        {
            var color = new FormatConvertedBitmap(image, PixelFormats.Bgra32, null, 0);
            int stride = color.PixelWidth * 4;
            byte[] header = new byte[8];
            BitConverter.GetBytes(color.PixelWidth).CopyTo(header, 0);
            BitConverter.GetBytes(color.PixelHeight).CopyTo(header, 4);
            byte[] pixels = new byte[stride * Math.Min(32, color.PixelHeight)];
            using (var sha = SHA256.Create())
            {
                sha.TransformBlock(header, 0, header.Length, header, 0);
                for (int y = 0; y < color.PixelHeight; y += 32)
                {
                    int height = Math.Min(32, color.PixelHeight - y);
                    color.CopyPixels(new Int32Rect(0, y, color.PixelWidth, height), pixels, stride, 0);
                    sha.TransformBlock(pixels, 0, stride * height, pixels, 0);
                }
                sha.TransformFinalBlock(new byte[0], 0, 0);
                return Convert.ToBase64String(sha.Hash);
            }
        }
    }

    internal enum CaptureSource { Folder, Clipboard }

    internal sealed class CaptureReceipts
    {
        sealed class Receipt
        {
            public string Hash;
            public CaptureSource Source;
            public DateTime Time;
            public bool Paired;
        }

        readonly List<Receipt> recent = new List<Receipt>();

        public bool Accept(string hash, CaptureSource source, DateTime time)
        {
            recent.RemoveAll(r => time - r.Time > TimeSpan.FromSeconds(5));
            // 只合并文件夹与剪贴板对同一次截图的通知；连续截取相同内容仍可保留。
            var pair = recent.FirstOrDefault(r => !r.Paired && r.Hash == hash && r.Source != source);
            if (pair != null) { pair.Paired = true; return false; }
            recent.Add(new Receipt { Hash = hash, Source = source, Time = time });
            return true;
        }
    }

    internal sealed class CaptureItem
    {
        public readonly string Path;
        public ImageContent Image;
        // 上绳时间（UTC），隔天下绳按它判断图片是否属于新的一天。
        public DateTime Hung;
        public DateTime Written;

        public CaptureItem(string path, ImageContent image)
        {
            Path = System.IO.Path.GetFullPath(path);
            Image = image.ForFile(Path);
            Hung = DateTime.UtcNow;
            Written = File.GetLastWriteTimeUtc(Path);
        }
    }

    // 隔天下绳用的一天起点：凌晨 StartHour 之前仍算前一天，熬夜跨过零点时绳上的图片不会被取走。
    internal static class RopeDay
    {
        public const int StartHour = 4;

        public static DateTime Start(DateTime now)
        {
            DateTime day = now.Date;
            if (now.Hour < StartHour) day = day.AddDays(-1);
            return day.AddHours(StartHour);
        }
    }

    internal sealed class Gallery
    {
        public readonly List<CaptureItem> Items = new List<CaptureItem>();
        public readonly List<CaptureItem> Collected = new List<CaptureItem>();
        public readonly StateStore Store;
        public event Action Changed;

        public Gallery(StateStore store) { Store = store; }

        public bool Contains(string path) { return Items.Any(i => FileRules.SameFile(i.Path, path)); }

        public CaptureItem Collect(string path, ImageContent image)
        {
            var item = Collected.FirstOrDefault(i => FileRules.SameFile(i.Path, path));
            if (item != null) return item;
            item = new CaptureItem(path, image);
            Collected.Add(item);
            Save();
            Notify();
            return item;
        }

        public void Add(string path, ImageContent image) { Add(path, image, DateTime.UtcNow); }

        // hung 是上绳时间（UTC）：启动恢复时沿用保存的值，其余场合取当前时间。
        public void Add(string path, ImageContent image, DateTime hung)
        {
            if (Contains(path)) return;
            var item = Collected.FirstOrDefault(i => FileRules.SameFile(i.Path, path));
            if (item == null) { item = new CaptureItem(path, image); Collected.Add(item); }
            else if (item.Image != image) { item.Image = image.ForFile(path); item.Written = File.GetLastWriteTimeUtc(path); }
            item.Hung = hung;
            Items.Add(item);
            if (Items.Count > 50) Items.RemoveAt(0);
            Save();
            Notify();
        }

        // 启动时把保存时挂在绳上的图片放回绳子。hung 是保存的上绳时间表：恢复过程中每次保存都会重建
        // 内存里的那一份数据，所以由调用方留住原表；旧记录没有保存时按文件创建时间估算。
        public void Restore(string path, ImageContent image, Dictionary<string, DateTime> hung)
        {
            DateTime time;
            if (hung == null || !hung.TryGetValue(path, out time)) time = File.GetCreationTimeUtc(path);
            Add(path, image, time);
        }

        // 隔天下绳：取下上绳时间（本地）早于 dayStart 的图片，留在篮子里；keep 返回 true 的（如贴在桌面的）不动。
        public int TakeDownBefore(DateTime dayStart, Func<CaptureItem, bool> keep)
        {
            var expired = Items.Where(item => item.Hung.ToLocalTime() < dayStart && (keep == null || !keep(item))).ToArray();
            if (expired.Length > 0) RemoveMany(expired);
            return expired.Length;
        }

        // 贴在桌面的图片回到绳子时按现在重新计时，当天不会被隔天下绳取走。
        public void Rehang(CaptureItem item)
        {
            if (!Items.Contains(item)) return;
            DateTime previous = item.Hung;
            item.Hung = DateTime.UtcNow;
            try { Save(); }
            catch { item.Hung = previous; throw; }
        }

        public void Remove(CaptureItem item)
        {
            Items.Remove(item);
            Save();
            Notify();
        }

        public void RemoveMany(IEnumerable<CaptureItem> items)
        {
            var removed = new HashSet<CaptureItem>(items);
            var previous = Items.ToArray();
            if (Items.RemoveAll(item => removed.Contains(item)) == 0) return;
            try { Save(); }
            catch { Items.Clear(); Items.AddRange(previous); Store.State.Images = Items.Select(i => i.Path).ToList(); Store.State.Hung = HungTimes(); throw; }
            Notify();
        }

        public void Clear()
        {
            var previous = Items.ToArray();
            Items.Clear();
            try { Save(); }
            catch { Items.AddRange(previous); Store.State.Images = Items.Select(i => i.Path).ToList(); throw; }
            Notify();
        }

        public void Forget(CaptureItem item)
        {
            int hanging = Items.IndexOf(item), collected = Collected.IndexOf(item);
            Items.Remove(item);
            Collected.Remove(item);
            try { Save(); }
            catch
            {
                if (hanging >= 0) Items.Insert(hanging, item);
                if (collected >= 0) Collected.Insert(collected, item);
                Store.State.Images = Items.Select(i => i.Path).ToList();
                Store.State.Hung = HungTimes();
                Store.State.Collection = Collected.Select(i => i.Path).ToList();
                throw;
            }
            Notify();
        }

        public CaptureItem Replace(CaptureItem item, string path)
        {
            int hanging = Items.IndexOf(item), collected = Collected.IndexOf(item);
            if (collected < 0) return null;
            // 编辑只换文件，图片仍在绳上原来的位置，上绳时间沿用。
            var copy = new CaptureItem(path, item.Image); copy.Hung = item.Hung;
            if (hanging >= 0) Items[hanging] = copy;
            Collected[collected] = copy;
            try { Save(); }
            catch
            {
                if (hanging >= 0) Items[hanging] = item;
                Collected[collected] = item;
                Store.State.Images = Items.Select(i => i.Path).ToList();
                Store.State.Hung = HungTimes();
                Store.State.Collection = Collected.Select(i => i.Path).ToList();
                throw;
            }
            Notify();
            return copy;
        }

        public void Prune()
        {
            int removed = Items.RemoveAll(i => !File.Exists(i.Path));
            removed += Collected.RemoveAll(i => !File.Exists(i.Path));
            if (removed == 0) return;
            Save();
            Notify();
        }

        public void Notify() { if (Changed != null) Changed(); }

        void Save()
        {
            Store.State.Images = Items.Select(i => i.Path).ToList();
            Store.State.Collection = Collected.Select(i => i.Path).ToList();
            Store.State.Hung = HungTimes();
            Store.Save();
        }

        Dictionary<string, DateTime> HungTimes() { return Items.ToDictionary(i => i.Path, i => i.Hung); }
    }
}
