// imgfacts IMAGE.png CROP_TOP VIEW_W VIEW_H  -> JSON on stdout:
// {w,h,ocr:[{t,x,y,w,h,c}], grid:{gw,gh,rgb:[r,g,b,...]}}
// The image is cropped to rows [CROP_TOP, CROP_TOP+VIEW_H) and columns [0,VIEW_W) (the page viewport),
// text is found with the Vision framework (accurate level, no language correction), boxes in viewport px,
// and the viewport is averaged down to a grid of 128 columns (cells of VIEW_W/128 px, square).
import Foundation
import Vision
import CoreGraphics
import ImageIO
let a = CommandLine.arguments
guard a.count >= 5, let src = CGImageSourceCreateWithURL(URL(fileURLWithPath: a[1]) as CFURL, nil),
      let full = CGImageSourceCreateImageAtIndex(src, 0, nil) else { print("{\"error\":\"unreadable\"}"); exit(1) }
let top = Int(a[2])!, vw = Int(a[3])!, vh = Int(a[4])!
let cw = min(vw, full.width), ch = max(1, min(vh, full.height - top))
guard let img = full.cropping(to: CGRect(x: 0, y: top, width: cw, height: ch)) else { print("{\"error\":\"crop\"}"); exit(1) }
// grid
let gw = 128, cell = Double(cw) / Double(gw), gh = max(1, Int((Double(ch) / cell).rounded(.down)))
let cs = CGColorSpaceCreateDeviceRGB()
var buf = [UInt8](repeating: 0, count: gw * gh * 4)
let ctx = CGContext(data: &buf, width: gw, height: gh, bitsPerComponent: 8, bytesPerRow: gw * 4, space: cs,
                    bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue)!
ctx.interpolationQuality = .medium
ctx.setFillColor(CGColor(red: 1, green: 1, blue: 1, alpha: 1)); ctx.fill(CGRect(x: 0, y: 0, width: gw, height: gh))
ctx.draw(img, in: CGRect(x: 0, y: 0, width: Double(gw), height: Double(ch) / cell))
var rgb: [Int] = []
// CGContext rows are bottom-up in memory order of drawing coords; buffer row 0 is the top row.
for y in 0..<gh { for x in 0..<gw { let i = (y * gw + x) * 4; rgb += [Int(buf[i]), Int(buf[i+1]), Int(buf[i+2])] } }
// OCR
var items: [[String: Any]] = []
let req = VNRecognizeTextRequest { r, _ in
  for o in (r.results as? [VNRecognizedTextObservation]) ?? [] {
    guard let c = o.topCandidates(1).first else { continue }
    let b = o.boundingBox
    items.append(["t": c.string, "x": Int(b.minX * Double(cw)), "y": Int((1 - b.maxY) * Double(ch)),
                  "w": Int(b.width * Double(cw)), "h": Int(b.height * Double(ch)), "c": Double(c.confidence)])
  }
}
req.recognitionLevel = .accurate
req.usesLanguageCorrection = false
try? VNImageRequestHandler(cgImage: img, options: [:]).perform([req])
let out: [String: Any] = ["w": cw, "h": ch, "ocr": items, "grid": ["gw": gw, "gh": gh, "rgb": rgb]]
let d = try! JSONSerialization.data(withJSONObject: out)
FileHandle.standardOutput.write(d)
