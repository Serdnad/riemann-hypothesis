module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapPderiv
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsHodgeTateDatumPolarisedAbelianCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle053
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle041
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle058
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem colength_bound_split_place_chart : ∀ (p : ℕ) [Fact p.Prime], AvFSt p := by
  intro p _ T _ _ _ _ _ _ hpT G _ _ D A U d F x hx OE _ _ _ _ _ _ _ io oD oA hlin act hact
    C _ _ _ v O _ _ hv _ _ _ iota hiota w t vd hvd rp rm W hW hW'
  obtain ⟨X, hX, hXr⟩ := GlobalTheory.T.exists_nilChart_reads_of_isChartJ T G U.smooth d F x hx
  have hread := hXr OE io act hact
  obtain ⟨FB, XB, hXB⟩ := GlobalTheory.T.exists_nilpotentGroupChart_smooth_commGroup T D.toPre.P.A D.toPre.P.g D.toPre.P.smoothDim
  have hαB : ∀ a : OE, ∃ φ : Fin D.toPre.P.g → PS T 1 D.toPre.P.g, Reads XB XB (oD.onB.act a) φ :=
    fun a => GlobalTheory.T.exists_powerSeries_reading_groupHom_nilpotentCharts T D.toPre.P.A D.toPre.P.A _ _ FB.F FB.F XB XB hXB hXB _ (oD.onB.hom a)
  choose αB hαB using hαB
  obtain ⟨r, J, Q, hext, heq⟩ := GlobalTheory.T.uniformization_split_formal_group_law_equivariant T _ D A G U d _ F FB X XB hX hXB
  obtain ⟨N, hN⟩ := heq OE io oD oA hlin act.act αB hread hαB
  obtain ⟨hlaw, hlinm, hextm⟩ := GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff T O iota
  obtain ⟨F', hF'⟩ := hlaw d F
  obtain ⟨FB', hFB'⟩ := hlaw _ FB
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formalGroupAction_linearPart_ringHom T d F OE act O iota
  have hext' := hextm d _ r F FB J Q hext
  have hFH : FH p F'.F := by
    intro k
    rw [hF']
    obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.FormalTorsion.fhSt p T hpT G D A U d F x hx C v O hv iota hiota k
    exact ⟨h1, h2, h4⟩
  have hB := GlobalTheory.T.exists_hodgeTateDatum_polarisedAbelian_characters p C v O hv T iota D.toPre.P _ rfl OE oD.onB FB XB hXB αB hαB
  rw [← hF', ← hFB'] at hext'
  rw [← hFB'] at hB
  obtain ⟨cp, hS, H, B, m, u, hu, hL⟩ := GlobalTheory.T.exists_linearData_of_split_formalGroup_extension p C v O hv OE d _ r F' FB' _ _ hext' hFH ρ N
    (fun a j => MvPowerSeries.map iota (αB a j))
    (fun a => by
      rw [hlinm, hlinm, (hρ a).2, ← Matrix.map_mul, ← Matrix.map_mul, (hN a).1])
    (fun a => by
      rw [hlinm, (hρ a).2, ← Matrix.map_mul, (hN a).2, Matrix.map_mul, Matrix.map_map]
      congr 2
      funext z
      simp) hB
  have hρf : (ρ : OE → Matrix (Fin d) (Fin d) O) = fun a => _root_.ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (actMap iota act a) :=
    funext fun a => (hρ a).1
  obtain ⟨xs, hxs, hle⟩ := GlobalTheory.T.colength_bound_split_place_linear_data p C v O hv OE cp hS _ H d r m _ B ρ N _ hL w t vd hvd rp rm W
    (fun j => by rw [hρf]; exact (isEigBasis_iff _ _ _).1 (hW j))
    (fun τ hτ => by
      obtain ⟨W', h⟩ := hW' τ hτ
      exact ⟨W', by rw [hρf]; exact (isEigBasis_iff _ _ _).1 h⟩)
  refine ⟨xs, fun j => ⟨m, u, fun k => ?_, hxs j⟩, hle⟩
  rw [← hF']
  exact hu k

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem unramified_companion_chart_characters : ∀ (p : ℕ) [Fact p.Prime], UpFSt p := by
  intro p hp T _ _ _ _ _ hT hpT G _ _ D A U d F x hx hp2 OE _ _ _ _ _ _ _ io oD oA hlin hdisc act hact
    C _ _ _ v O _ _ hv _ hO _ _ iota hio w _ t _ hfrob r W hW j
  obtain ⟨X, hX, hXr⟩ := GlobalTheory.T.exists_nilChart_reads_of_isChartJ T G U.smooth d F x hx
  have hreadG := hXr OE io act hact
  obtain ⟨FB, XB, hXB⟩ := GlobalTheory.T.exists_nilpotentGroupChart_smooth_commGroup T D.toPre.P.A D.toPre.P.g D.toPre.P.smoothDim
  have hB : ∀ a : OE, ∃ φ, Reads XB XB (oD.onB.act a) φ := fun a =>
    GlobalTheory.T.exists_powerSeries_reading_groupHom_nilpotentCharts T _ _ _ _ _ _ XB XB hXB hXB _ (oD.onB.hom a)
  choose αB hαB using hB
  obtain ⟨rk, J, Q, hext, heq⟩ := GlobalTheory.T.uniformization_split_formal_group_law_equivariant T _ D A G U d _ F FB X XB hX hXB
  obtain ⟨N, hN⟩ := heq OE io oD oA hlin act.act αB hreadG hαB
  obtain ⟨hlaw, hlinmap, hextmap⟩ := GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff T O iota
  obtain ⟨F', hF'⟩ := hlaw d F
  obtain ⟨FB', hFB'⟩ := hlaw _ FB
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formalGroupAction_linearPart_ringHom T d F OE act O iota
  have hFH : FH p F'.F := by
    intro k
    rw [hF']
    obtain ⟨h1, h2, -, h4⟩ :=
      GlobalTheory.FormalTorsion.fhSt p T hpT G D A U d F x hx C v O hv iota hio k
    exact ⟨h1, h2, h4⟩
  have hext' : ExtSer F'.F FB'.F (fun j => MvPowerSeries.map iota (J j))
      (fun j => MvPowerSeries.map iota (Q j)) := by
    rw [hF', hFB']
    exact hextmap _ _ _ F FB J Q hext
  have hht := GlobalTheory.T.exists_hodgeTateDatum_polarisedAbelian_characters p C v O hv T iota D.toPre.P _ rfl OE oD.onB FB XB hXB αB hαB
  rw [← hFB'] at hht
  obtain ⟨cp, hset, H, B, m, u, hu, hdat⟩ := GlobalTheory.T.exists_linearData_of_split_formalGroup_extension p C v O hv OE d _ rk F' FB' _ _ hext' hFH ρ N
    (fun a j => MvPowerSeries.map iota (αB a j))
    (fun a => by
      rw [hlinmap, hlinmap, (hρ a).2, ← Matrix.map_mul, ← Matrix.map_mul, (hN a).1])
    (fun a => by
      rw [hlinmap, (hρ a).2, ← Matrix.map_mul, (hN a).2, Matrix.map_mul, Matrix.map_map]
      congr 2
      ext z
      simp)
    hht
  have hρ' : (ρ : OE → Matrix (Fin d) (Fin d) O) = fun a => _root_.ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (actMap iota act a) :=
    funext fun a => (hρ a).1
  obtain ⟨xs, hxs, hle⟩ := GlobalTheory.T.linearData_unramified_length_bound p C v O hv OE cp hset _ H d rk m _ B ρ N _ hdat hp2 hdisc w t hfrob r W
    (fun τ => by rw [hρ']; exact (isEigBasis_iff _ _ _).1 (hW τ)) j
  refine ⟨xs, ⟨m, u, ?_, hxs⟩, hle⟩
  rw [← hF']
  exact hu

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodgeTate_inclusion_chart_characters : ∀ (p : ℕ) [Fact p.Prime], HTFSt p := by
  first | exact @GlobalTheory.ChF.hodgeTate_inclusion_chart | exact GlobalTheory.ChF.hodgeTate_inclusion_chart | (intros; apply GlobalTheory.ChF.hodgeTate_inclusion_chart <;> assumption)
end
