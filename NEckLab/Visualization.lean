import NEckLab.RegularPolygon
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

namespace NEckLab

open ProofWidgets Svg

/-!
A computational visualization layer for the exact `RegularPolygon` model.
The formal geometry remains in `ℝ`/`ℂ`; this module uses `Float` only to draw
an inspectable approximation in the VS Code InfoView.
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

/-- Static InfoView rendering of a regular polygon together with its limiting unit circle. -/
def regularPolygonSvg (n : ℕ) : Svg vizFrame :=
  { elements := #[
      circle (0.0, 0.0) (.abs 1.0)
        |>.setStroke (110., 110., 110.) (.px 1),
      polygon (approxVertices n)
        |>.setStroke (220., 220., 220.) (.px 2)
        |>.setFill (0.12, 0.12, 0.12),
      text (-1.12, -1.08) s!"n = {n}" (.px 18)
        |>.setFill (210., 210., 210.)
    ] }

private def triangleView := regularPolygonSvg 3
private def squareView := regularPolygonSvg 4
private def pentagonView := regularPolygonSvg 5
private def twentyView := regularPolygonSvg 20

-- Place the cursor on one of these commands to inspect the geometry in VS Code.
#html triangleView.toHtml
#html squareView.toHtml
#html pentagonView.toHtml
#html twentyView.toHtml

end NEckLab
