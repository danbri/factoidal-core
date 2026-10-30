// SVG's explicit storage mode is interpreted from the Lean render plan.
import type {SVGArtifact} from "./svg_engine.ts";
import {render} from "./gpu_transport.ts";
export {unpad,encodePPM,checkPixels} from "./gpu_transport.ts";
export const renderSVG=(artifact:SVGArtifact)=>render(artifact,"svg-offscreen");
