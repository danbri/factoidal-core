/-
L4Factoidal.Media.Tests: tests of the Ogg and WebM readers (`lake exe media-bench
test`, from `formal/lean4`). The files are in `third_party/media/` (made for these
tests; see its README). The expected counts are those of `ffprobe -count_packets`
(FFmpeg 9.0.1), plus the codec header packets that it does not count in Ogg.
-/
import L4Factoidal.Media.Ogg
import L4Factoidal.Media.WebM
import L4Factoidal.Media.Mp3
import L4Factoidal.Media.Wav
import L4Factoidal.Media.Decode

namespace L4Factoidal.Media.Tests
open L4Factoidal.Media

def mediaDir : System.FilePath := "../../third_party/media"

structure Tally where
  pass : Nat := 0
  fail : Nat := 0

def check (t : Tally) (name : String) (ok : Bool) (detail : String := "") : IO Tally := do
  if ok then return { t with pass := t.pass + 1 }
  IO.println s!"FAIL {name} {detail}"
  return { t with fail := t.fail + 1 }

def bytes (l : List Nat) : ByteArray := ⟨(l.map (·.toUInt8)).toArray⟩

def run : IO Bool := do
  let mut t : Tally := {}
  -- CRC-32 of the Ogg polynomial: the CRC of "123456789" with this table and no
  -- reflection or final XOR (CRC-32/MPEG-2 without the initial all-ones) is 0x89A1897F.
  let digits := "123456789".toUTF8
  let c := Id.run do
    let mut c : UInt32 := 0
    for i in [0:digits.size] do
      c := (c <<< 8) ^^^ Ogg.crcTable[(((c >>> 24) ^^^ digits[i]!.toUInt32) &&& 0xFF).toNat]!
    return c
  t ← check t "crc of 123456789" (c == 0x89A1897F) s!"{c}"
  -- Variable-size integers (RFC 8794 section 4.4 examples): 1 as 0x81, 0x4001, 0x200001.
  t ← check t "vint 0x81" ((WebM.vint (bytes [0x81]) 0).toOption.map (·.2.1) == some 1)
  t ← check t "vint 0x4001" ((WebM.vint (bytes [0x40, 0x01]) 0).toOption.map (·.2.1) == some 1)
  t ← check t "vint 0x200001" ((WebM.vint (bytes [0x20, 0x00, 0x01]) 0).toOption.map (·.2.1) == some 1)
  t ← check t "vint unknown size" ((WebM.vint (bytes [0xFF]) 0).toOption.map (·.2.2) == some true)
  t ← check t "vint 0x00 refused" ((WebM.vint (bytes [0x00]) 0).toOption.isNone)
  -- Lacing (RFC 9559 section 10.3): 3 frames of 800, 500 and 1000 bytes.
  let xiph := bytes ([2] ++ [255, 255, 255, 35] ++ [255, 245]) ++ ByteArray.mk (Array.replicate 2300 0)
  t ← check t "Xiph lacing" ((WebM.laceSizes xiph 1 0 xiph.size).toOption.map (·.2) == some #[800, 500, 1000])
  -- EBML lacing: 800 as 0x4320, then 500 - 800 = -300 as a 2-byte signed value
  -- (raw = -300 + 8191 = 7891 = 0x1ED3, with the marker: 0x5ED3).
  let ebml := bytes [2, 0x43, 0x20, 0x5E, 0xD3] ++ ByteArray.mk (Array.replicate 2300 0)
  t ← check t "EBML lacing" ((WebM.laceSizes ebml 3 0 ebml.size).toOption.map (·.2) == some #[800, 500, 1000])
  let fixed := bytes [2] ++ ByteArray.mk (Array.replicate 2400 0)
  t ← check t "fixed lacing" ((WebM.laceSizes fixed 2 0 fixed.size).toOption.map (·.2) == some #[800, 800, 800])
  -- Ogg Opus file: 1 stream, OpusHead, 2 header packets and 201 audio packets.
  let opus ← IO.FS.readBinFile (mediaDir / "arpeggio.opus")
  let r := Ogg.demux opus
  t ← check t "ogg opus: one stream" (r.streams.size == 1)
  t ← check t "ogg opus: no dropped pages" (r.dropped == 0)
  let s := r.streams[0]!
  t ← check t "ogg opus: codec" (s.codec == .opus)
  t ← check t "ogg opus: 203 packets" (s.packets.size == 203) s!"{s.packets.size}"
  t ← check t "ogg opus: OpusHead" (match Ogg.opusHead s.packets[0]!.data with
    | .ok h => h.channels == 2 && h.preSkip == 312 && h.mapping == 0 | .error _ => false)
  t ← check t "ogg opus: end of stream" s.eos
  -- 4 s at 48 kHz plus the pre-skip.
  t ← check t "ogg opus: last granule" (s.lastGranule.toNat == 192000 + 312) s!"{s.lastGranule}"
  -- One changed byte in the second page: that page is dropped, the rest still read.
  let (_, len0) := (Ogg.readPage opus 0).toOption.getD (default, 0)
  let bad := opus.set! (len0 + 40) (opus[len0 + 40]! ^^^ 0xFF)
  let rb := Ogg.demux bad
  t ← check t "ogg: a page with a bad CRC is dropped" (rb.dropped == 1 && rb.pages + 1 == r.pages)
    s!"dropped {rb.dropped}, pages {rb.pages} of {r.pages}"
  -- Ogg Vorbis: 3 header packets and 174 audio packets.
  let vb ← IO.FS.readBinFile (mediaDir / "arpeggio.ogg")
  let rv := Ogg.demux vb
  t ← check t "ogg vorbis: codec" (rv.streams.size == 1 && rv.streams[0]!.codec == .vorbis)
  t ← check t "ogg vorbis: 177 packets" (rv.streams[0]!.packets.size == 177) s!"{rv.streams[0]!.packets.size}"
  t ← check t "ogg vorbis: identification" ((Ogg.vorbisId rv.streams[0]!.packets[0]!.data).toOption == some (2, 44100))
  -- WebM with VP8 and Opus.
  let w ← IO.FS.readBinFile (mediaDir / "testsrc-320x180.webm")
  match WebM.demux w with
  | .error e => t ← check t "webm 320x180" false e
  | .ok r =>
    t ← check t "webm: DocType" (r.docType == "webm")
    t ← check t "webm: two tracks" (r.tracks.size == 2)
    let v := r.tracks.find? (·.codec == "V_VP8")
    let a := r.tracks.find? (·.codec == "A_OPUS")
    t ← check t "webm: VP8 320x180" (v.map (fun v => v.width == 320 && v.height == 180) == some true)
    t ← check t "webm: Opus 48 kHz stereo" (a.map (fun a => a.rate == 48000 && a.channels == 2) == some true)
    t ← check t "webm: Opus CodecPrivate is OpusHead" (a.map (fun a => Ogg.codecOf a.codecPrivate == .opus) == some true)
    let nv := (v.map fun v => (r.framesOf v.number).size).getD 0
    let na := (a.map fun a => (r.framesOf a.number).size).getD 0
    t ← check t "webm: 48 video frames" (nv == 48) s!"{nv}"
    t ← check t "webm: 101 audio frames" (na == 101) s!"{na}"
    let vf := (v.map fun v => r.framesOf v.number).getD #[]
    t ← check t "webm: first video frame is a key frame" (vf[0]?.map (·.key) == some true)
    t ← check t "webm: frame times rise" ((List.range (vf.size - 1)).all fun i => vf[i]!.time < vf[i+1]!.time)
    t ← check t "webm: last frame at 47/24 s" (vf.back?.map (·.time) == some 1958000000) s!"{vf.back?.map (·.time)}"
  let w2 ← IO.FS.readBinFile (mediaDir / "testsrc-160x90.webm")
  match WebM.demux w2 with
  | .error e => t ← check t "webm 160x90" false e
  | .ok r =>
    t ← check t "webm 160x90: VP8 and Vorbis tracks" (r.tracks.size == 2 &&
      r.tracks.any (·.codec == "V_VP8") && r.tracks.any (·.codec == "A_VORBIS"))
    let v := r.tracks.find? (·.codec == "V_VP8")
    let a := r.tracks.find? (·.codec == "A_VORBIS")
    t ← check t "webm 160x90: 48 video frames, 88 audio frames"
      ((v.map fun v => (r.framesOf v.number).size) == some 48 && (a.map fun a => (r.framesOf a.number).size) == some 88)
    -- Vorbis CodecPrivate: three Xiph-laced header packets, the first the identification header.
    t ← check t "webm 160x90: Vorbis headers from CodecPrivate"
      (match a.map (fun a => WebM.xiphHeaders a.codecPrivate) with
       | some (.ok hs) => hs.size == 3 && (Ogg.vorbisId hs[0]!).toOption == some (2, 44100)
       | _ => false)
  -- A file cut short in the middle reads up to the cut, without an error.
  match WebM.demux (w.extract 0 (w.size / 2)) with
  | .error e => t ← check t "webm cut short" false e
  | .ok r => t ← check t "webm cut short: some frames" (r.frames.size > 10 && r.frames.size < 149)
  -- MP3 (Media.Mp3): the three clips of 2026-11-26. The two 44.1 kHz stereo files start with an
  -- information frame whose LAME header gives delay 576 and padding 1584: 155 audio frames of 1152
  -- samples, of which 576 + 529 are dropped at the start and 176400 (4 s) kept, as FFmpeg does.
  for (name, frames, rate, ch, skip, keep) in [("arpeggio-cbr128.mp3", 155, 44100, 2, 1105, some 176400),
      ("arpeggio-vbr.mp3", 155, 44100, 2, 1105, some 176400),
      ("arpeggio-mono22.mp3", 156, 22050, 1, 0, none)] do
    match Mp3.read (← IO.FS.readBinFile (mediaDir / name)) with
    | .error e => t ← check t s!"mp3 {name}" false e
    | .ok r =>
      t ← check t s!"mp3 {name}: frames, rate, channels, gapless"
        (r.frames.size == frames && r.header.rate == rate && r.header.channels == ch && r.skip == skip && r.keep == keep)
        s!"{r.frames.size} frames, {r.header.rate} Hz, {r.header.channels} channels, skip {r.skip}, keep {r.keep}, info {repr r.info}"
  -- A cut file reads the whole frames before the cut.
  let mp ← IO.FS.readBinFile (mediaDir / "arpeggio-cbr128.mp3")
  match Mp3.read (mp.extract 0 (mp.size / 2)) with
  | .error e => t ← check t "mp3 cut short" false e
  | .ok r => t ← check t "mp3 cut short: some frames" (r.frames.size > 50 && r.frames.size < 100) s!"{r.frames.size}"
  -- Junk before the first frame is skipped; junk that is not MP3 is refused.
  let junk := ByteArray.mk (Array.replicate 1000 0x55)
  match Mp3.read (junk ++ mp) with
  | .error e => t ← check t "mp3 after junk" false e
  | .ok r => t ← check t "mp3 after junk: same frames" (r.frames.size == 155 && r.keep == some 176400) s!"{r.frames.size}"
  t ← check t "mp3 refuses bytes that are not MP3" (Mp3.read junk).toOption.isNone
  -- WAV (Media.Wav): conversions, chunk walking, refusals (more in the `#guard`s of Wav.lean).
  let w16 := Wav.build 1 2 44100 16 (bytes [0x00, 0x40, 0x00, 0xC0, 0xFF, 0x7F, 0x00, 0x80])
  match Wav.read w16 with
  | .error e => t ← check t "wav 16-bit" false e.describe
  | .ok r =>
    t ← check t "wav 16-bit stereo: frames, rate, channels"
      (r.frames == 2 && r.format.rate == 44100 && r.format.channels == 2 && r.format.bits == 16)
    t ← check t "wav 16-bit: values are sample / 32768"
      (r.samples[0]!.data.toList == [0.5, 32767.0 / 32768.0] && r.samples[1]!.data.toList == [-0.5, -1.0])
  -- The writer of Media.Decode and this reader agree: the samples come back as s16 / 32768.
  let pcm : Decode.Pcm := { rate := 8000, channels := 1, samples := bytes [0x34, 0x12, 0xCB, 0xED], steps := 0, ns := 0, packets := 0 }
  match Wav.read (Decode.wav pcm) with
  | .error e => t ← check t "wav written by Decode.wav" false e.describe
  | .ok r =>
    let ok := r.samples[0]!.data.toList == [4660.0 / 32768.0, -4661.0 / 32768.0] && r.format.rate == 8000
    t ← check t "wav written by Decode.wav reads back" ok s!"{r.samples[0]!.data.toList}"
  t ← check t "wav: a cut file reads the frames before the cut" ((Wav.read (w16.extract 0 (w16.size - 2))).toOption.map (·.frames) == some 1)
  t ← check t "wav refuses an Ogg file" ((Wav.read opus).toOption.isNone)
  t ← check t "wav refuses RIFX" ((Wav.read (Wav.ascii "RIFX" ++ Wav.le32 0 ++ Wav.ascii "WAVE")).toOption.isNone)
  t ← check t "wav: 12 bytes of WAVE without chunks is no fmt" ((Wav.read (Wav.ascii "RIFF" ++ Wav.le32 4 ++ Wav.ascii "WAVE")).toOption.isNone)
  -- A float WAV with a NaN, an infinity and a normal value: the first two are replaced and counted.
  match Wav.read (Wav.build 3 1 8000 32 (bytes [0, 0, 0xC0, 0x7F, 0, 0, 0x80, 0xFF, 0, 0, 0, 0x3F])) with
  | .error e => t ← check t "wav float non-finite" false e.describe
  | .ok r =>
    let ok := r.samples[0]!.data.toList == [0.0, 0.0, 0.5] && r.nonFinite == 2
    t ← check t "wav float: NaN and -infinity become 0, counted" ok
  IO.println s!"media tests: {t.pass} pass, {t.fail} fail"
  return t.fail == 0

end L4Factoidal.Media.Tests
