/-
L4Factoidal.Media.Tests: tests of the Ogg and WebM readers (`lake exe media-bench
test`, from `formal/lean4`). The files are in `third_party/media/` (made for these
tests; see its README). The expected counts are those of `ffprobe -count_packets`
(FFmpeg 9.0.1), plus the codec header packets that it does not count in Ogg.
-/
import L4Factoidal.Media.Ogg
import L4Factoidal.Media.WebM

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
  IO.println s!"media tests: {t.pass} pass, {t.fail} fail"
  return t.fail == 0

end L4Factoidal.Media.Tests
