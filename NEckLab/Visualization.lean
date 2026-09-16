import NEckLab.RegularPolygon
import NEckLab.TwoAxis
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

namespace NEckLab

open ProofWidgets Svg

/-!
Gate 10: a computational visualization layer for the exact research model.
The formal geometry remains in `ℝ`/`ℂ`; this module uses `Float` only to draw
inspectable approximations in the VS Code InfoView.
-/

private def vizFrame : Frame where
  xmin := -1.25
  ymin := -1.25
  xSize := 2.5
  width := 420
  height := 420

private def approxTau : Float := 6.283185307179586

/-- Executable shadow of the exact angle `2π k / n`, used only for rendering. -/
def approxVertex (n k : ℕ) : Float × Float :=
  if n = 0 then
    (0.0, 0.0)
  else
    let θ := approxTau * Float.ofNat k / Float.ofNat n
    (Float.cos θ, Float.sin θ)

/-- Approximate vertices in the same cyclic order as the exact `vertex` map. -/
def approxVertices (n : ℕ) : Array (Float × Float) :=
  (List.range n).map (approxVertex n) |>.toArray

/-- Adapt computational coordinate pairs to the frame-indexed SVG point type. -/
private def approxSvgPoints (n : ℕ) : Array (Point vizFrame) :=
  (approxVertices n).map fun (p : Float × Float) => (p : Point vizFrame)

/-- Static InfoView rendering of a regular polygon together with its limiting unit circle. -/
def regularPolygonSvg (n : ℕ) : Svg vizFrame :=
  { elements := #[
      circle (0.0, 0.0) (.abs 1.0)
        |>.setStroke (0.43, 0.43, 0.43) (.px 1),
      polygon (approxSvgPoints n)
        |>.setStroke (0.86, 0.86, 0.86) (.px 2)
        |>.setFill (0.12, 0.12, 0.12),
      text (-1.12, -1.08) s!"n = {n}" (.px 18)
        |>.setFill (0.82, 0.82, 0.82)
    ] }

/-- Gate 10: overlay several finite polygon stages against the limiting circle. -/
def convergenceOverlaySvg : Svg vizFrame :=
  { elements := #[
      circle (0.0, 0.0) (.abs 1.0)
        |>.setStroke (0.95, 0.95, 0.95) (.px 2),
      polygon (approxSvgPoints 3)
        |>.setStroke (0.35, 0.35, 0.35) (.px 1),
      polygon (approxSvgPoints 4)
        |>.setStroke (0.45, 0.45, 0.45) (.px 1),
      polygon (approxSvgPoints 6)
        |>.setStroke (0.58, 0.58, 0.58) (.px 1),
      polygon (approxSvgPoints 12)
        |>.setStroke (0.72, 0.72, 0.72) (.px 1),
      polygon (approxSvgPoints 40)
        |>.setStroke (0.86, 0.86, 0.86) (.px 1),
      text (-1.12, -1.08) "n = 3, 4, 6, 12, 40 → circle" (.px 15)
        |>.setFill (0.82, 0.82, 0.82)
    ] }

private def approxTriangleContract (j : ℕ) (p : Float × Float) : Float × Float :=
  let c := approxVertex 3 j
  ((p.1 + c.1) / 2.0, (p.2 + c.2) / 2.0)

/-- Computational shadow of the three-map self-similar refinement from Gate 8. -/
def approxFractalCloud : ℕ → Array (Float × Float)
  | 0 => #[(0.0, 0.0)]
  | depth + 1 =>
      let prev := approxFractalCloud depth
      (prev.map (approxTriangleContract 0)) ++
      (prev.map (approxTriangleContract 1)) ++
      (prev.map (approxTriangleContract 2))

private def fractalPointElements (depth : ℕ) : Array (Element vizFrame) :=
  (approxFractalCloud depth).map fun (p : Float × Float) =>
    circle (p : Point vizFrame) (.px 2)
      |>.setFill (0.88, 0.88, 0.88)

/-- Gate 10: inspect a finite fractal-refinement depth next to the same triangle geometry. -/
def fractalApproxSvg (depth : ℕ) : Svg vizFrame :=
  { elements := #[
      polygon (approxSvgPoints 3)
        |>.setStroke (0.45, 0.45, 0.45) (.px 1),
      text (-1.12, -1.08) s!"triangle refinement depth m = {depth}" (.px 15)
        |>.setFill (0.82, 0.82, 0.82)
    ] ++ fractalPointElements depth }

private def triangleView := regularPolygonSvg 3
private def squareView := regularPolygonSvg 4
private def pentagonView := regularPolygonSvg 5
private def twentyView := regularPolygonSvg 20
private def convergenceView := convergenceOverlaySvg
private def fractalDepthFiveView := fractalApproxSvg 5

-- Place the cursor on one of these commands to inspect the research objects in VS Code.
#html triangleView.toHtml
#html squareView.toHtml
#html pentagonView.toHtml
#html twentyView.toHtml
#html convergenceView.toHtml
#html fractalDepthFiveView.toHtml

end NEckLab
