module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle030
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle045
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

theorem evR_eq_clsSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂), FrOver d y₂ y → IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y₂.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk → A.Marked mk → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), LatsOK d.l₂.M La Nc → (∀ k, io (xs k) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ k, IsRoots d.l₂ L mk (Nc k) (Y k)) → ∀ f : Rul Xo c, IsThClsD Xo c d w La Nc gam vol ep io xs f → evR Xo c f y = evR d.Xo₂ d.c₂ d.cδ y₂ * κ * clsSum (algebraMap c.F ℂ) X hr bas idx eL w La Nc gam vol ep (fun k => io (xs k)) L v Y x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hF ⟨inst, hnab⟩ r g X bas idx e x L y y₂ A hov hs hx hL q0 hr eL hr' hn
    hlet θ v κ hread hvac hκ mk hmk hA Cl _ w La Nc gam vol ep Vs _ _ io xs a hLa hH Y hY f hf
  obtain ⟨vc, hvc, hev⟩ := hf ℂ hF y y₂ hov
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = algebraMap c.F ℂ :=
    RingHom.ext fun t => hF t
  rw [hev, mul_assoc, clsSum, Finset.mul_sum _ _ κ]
  refine congrArg (fun t => evR d.Xo₂ d.c₂ d.cδ y₂ * t) (Finset.sum_congr rfl fun k _ => ?_)
  obtain ⟨h1, h2, h3⟩ := hLa k
  have hV : (La k).La ∈ Vset E n d.l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset E n (La k).La).2.1 _ (Nc k) d.l₂.odd.pos h1 h2 h3
  have hP := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hH k)
  have h := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X bas idx e x L y₂ A hs hx hL q0 n hr eL hr' hn hlet
    d.nab₂ hnab θ v κ hread hvac hκ mk hmk hA (La k).La hV (Nc k) h3 (Y k) (hY k) a _ hP _ 1 (vc k) (hvc k)
  rw [h, MvPolynomial.map_map, hcomp]
  simp only [hF, map_mul, map_inv₀, map_natCast, inv_one, map_one]
  ring

end GlobalTheory.ClsVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU perFr
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ReadAll

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

theorem isSB_smul' (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  refine ⟨R, hR, fun x hx => hsupp x fun h0 => hx (by simp [h0]), fun x y hy => ?_⟩
  simp only [Pi.smul_apply, hper x y hy]

theorem isSB_finsum {J : Sort*} {f : J → TF n g} (h : ∀ i, IsSB (f i)) : IsSB (∑ᶠ i, f i) := by
  rw [finsum_def']
  split_ifs with hfin
  · exact Finset.sum_induction _ IsSB
      (fun φ ψ hφ hψ => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ ψ hφ hψ).1)
      isSB_zero (fun i _ => h i.down)
  · exact isSB_zero

theorem isSB_phiF {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (he : Even n) (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (hn : r ≤ n)
    (v₀ : Lt E r → TF n g) (L : Lt E r) (Λ : Lt E n) (hv : IsSB (v₀ L)) :
    IsSB (phiF bas D 𝔐 hn v₀ L Λ) := by
  have hH : ∀ (y : Matrix (Fin n) (Fin r) E) (φ : TF n g), IsSB φ → IsSB (heisG X bas y φ) :=
    fun y φ hφ => ((heisG_laws E r X g bas idx n hs he).2.2.2 y φ hφ).1
  have hP : IsSB (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
    unfold projA
    refine isSB_smul' _ (isSB_finsum fun ψ => isSB_finsum fun hψ => ?_)
    obtain ⟨y, -, rfl⟩ := hψ
    exact isSB_smul' _ (hH y _ hv)
  unfold phiF unitv
  exact isSB_finsum fun c => isSB_smul' _ (hH _ _ (isSB_smul' _ hP))

theorem perFr_cast {X' X : Data E r} (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨hp, hg, h0, hxi, hka⟩ := h
  cases X'
  cases X
  dsimp only at hp hg h0 hxi hka
  subst hp hg h0 hxi hka
  unfold Formalism.L2.PjFree.perFr
  rfl


private theorem differentiableOn_and_bchar_equivariant_lact_castFr {X' X : Data E r} (h : SameSp X' X) {ga : GL (Fin r) E} (hUn : IsUn X ga)
    {la : Wt X.Ψ r} {la' : Wt X'.Ψ r} (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i)
    (Q : Frame X.Ψ r → ℂ) (hQ : DifferentiableOn ℂ Q X.dom)
    (hw : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) (c0 : ℂ) :
    DifferentiableOn ℂ (fun x => c0 * Q (lact ga (castFr h.psi x))) X'.dom ∧
      ∀ x ∈ X'.dom, ∀ b ∈ Bor X'.Ψ r,
        c0 * Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * (c0 * Q (lact ga (castFr h.psi x))) := by
  have hm : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    GlobalTheory.Dict.Extend.lact_mem hUn (GlobalTheory.Dict.SameSp.castFr_mem_dom h hx)
  refine ⟨(hQ.comp ((GlobalTheory.Dict.Extend.differentiable_lact ga).comp
    (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn hm).const_mul c0, fun x hx b hb => ?_⟩
  rw [GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul, hw _ (hm x hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb),
    GlobalTheory.Dict.Pull.cast_bchar h.psi hl]
  ring

end GlobalTheory.Dict.ReadAll


open GlobalTheory.Dict.ReadAll GlobalTheory.Dict.Pull GlobalTheory.Dict.Extend in
theorem GlobalTheory.Dict.rdU_short_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (W : UW U) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ (Dc : Dic Dw c σ X W.g Dw.p n a) (D : SW.Level X) (hn : r ≤ n), Dc.e = W.e → LevTie d σ ph D hn → ∀ v₀ : Lt E r → TF n W.g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ (k : U.Comp) (h : SameSp (U.X k) X) (ga : GL (Fin r) E) (δ : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsUn X ga → mapL ga (U.X k).Λ ∈ D.lats → IsMark l (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) → IsDual X l (σ (zetaM c)) (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ C : ℂ, C ≠ 0 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f ∈ sec Xo c a n, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → ∀ x ∈ (U.X k).dom, rdU U f k x = C * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) (lact ga (castFr h.psi x)) := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hg hU hr hlev hnab hunitC ph ψ x₀ hpin W X a hdom Dc D hn hDe
    htie v₀ hvac x0
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI : Algebra d.c₂.F ℂ := (σ.comp d.eF.symm.toAlgHom.toRingHom).toAlgebra
  have hU' := hU
  unfold Formalism.L2.PjFree.IsUnf at hU'
  obtain ⟨hrpq, hk, -, -, hsec, -⟩ := hU'
  obtain ⟨u, hu0, hmain⟩ := GlobalTheory.Dict.ShortPt.shortRule_value hCI E H Dw l Xo c n d
    (fun t => by show σ (d.eF.symm (d.eF t)) = σ t; rw [AlgEquiv.symm_apply_apply])
    hlev hnab (fun y₂ => hunitC _ y₂) ph ψ x₀ hpin r W.g Dw.p X a Dc D hn hdom.2 hrpq htie v₀ hvac x0
  refine ⟨u, hu0, ?_⟩
  intro k h ga δ hUn hlat hmark hdual hx0
  obtain ⟨ρ, hρ, hall⟩ := hmain _ hlat _ δ hmark hdual hx0
  rw [hDe] at hall
  have hself : SelfD (U.X k) (U.X k).Λ := (GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hg hU hr W k).2.1
  have hvL : IsSB (v₀ (mapL ga (U.X k).Λ)) := (hvac _ hlat).1
  have hwt : ∀ (τ : X.Ψ) (i : Fin r),
      wtOf X Dc.hr Dc.k Dc.k' n τ i = laU U a n k ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i := by
    intro τ i
    rw [Dc.wt_eq]
    unfold wtX Formalism.L2.PjFree.laU
    simp only [h.p0]
  let Jx := {q : Lt E n × ℕ × (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ×
      (sec Xo c a n) // q.1 ∈ Vset E n d.l₂.M ∧ NOK q.1 q.2.1 d.l₂.M ∧
        IsShortRule Xo c d (⟨q.1⟩ : GenLat E n) q.2.1 x0 q.2.2.1.1 q.2.2.2.1}
  let R : Jx → Frame (U.X k).Ψ r → ℂ := fun i => rdU U i.1.2.2.2.1 k
  let T : Jx → Frame (U.X k).Ψ r → ℂ := fun i x => u i.1.1 i.1.2.1 *
    thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) i.1.1)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ i.1.2.2.1.1)) (lact ga (castFr h.psi x))
  have hol : ∀ i, DifferentiableOn ℂ (R i) (U.X k).dom ∧ DifferentiableOn ℂ (T i) (U.X k).dom ∧
      ∀ x ∈ (U.X k).dom, ∀ b ∈ Bor (U.X k).Ψ r,
        R i (rmul x b) = bchar (laU U a n k) b * R i x ∧ T i (rmul x b) = bchar (laU U a n k) b * T i x := by
    intro i
    have hs := hsec a n hdom i.1.2.2.2.1 i.1.2.2.2.2 k
    have ht := GlobalTheory.SW.theta_holomorphic_weight E r X W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 Dc.k Dc.k' _
      (GlobalTheory.Dict.ReadAll.isSB_phiF Dc.idx Dc.sympl hdom.2 D (Mfr l) hn v₀ _ i.1.1 hvL) _ (Dc.mem _ i.1.2.2.1.2)
    obtain ⟨hd, hw⟩ := GlobalTheory.Dict.ReadAll.differentiableOn_and_bchar_equivariant_lact_castFr h hUn hwt _ ht.1 ht.2.1 (u i.1.1 i.1.2.1)
    exact ⟨hs.1, hd, fun x hx b hb => ⟨hs.2.1 x hx b hb, hw x hx b hb⟩⟩
  have unit : ∀ x ∈ (U.X k).dom, IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x := by
    intro x hx hunit
    obtain ⟨Dc', hDe', -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n (U.X k) a W.e hg hrpq (hk k).1 (hk k).2
      hself hdom
    have hpv' : ∀ x v j, pv (U.X k) Dc'.idx x v j =
        perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2 := by
      rw [← hDe']; exact Dc'.per_eq
    have hrt' : ∀ j, rowType (U.X k) (Dc'.idx j) = Formalism.L2.PjFree.relab c σ (W.e j).1 := by
      rw [← hDe']; exact Dc'.ty_eq
    obtain ⟨A, hMk, θ, hRd, hMn⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hg hU hr W k Dc'.bas Dc'.idx
      Dc'.sympl hpv' hrt' ⟨x, hx⟩ hunit
    have hpv : ∀ v, pv (U.X k) Dc'.idx x v = pv X Dc.idx (castFr h.psi x) v := by
      intro v
      funext j
      rw [hpv', Dc.per_eq, hDe, GlobalTheory.Dict.ReadAll.perFr_cast h]
    have hrow : ∀ j, rowType (U.X k) (Dc'.idx j) = rowType X (Dc.idx j) := by
      intro j
      rw [hrt', Dc.ty_eq, hDe]
    obtain ⟨hxm, hun, -, A', hRd', hMn', hMk'⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c r W.g (U.X k) X h Dc'.bas
      Dc'.idx Dc.bas Dc.idx W.e x (U.X k).Λ (unC U k ⟨x, hx⟩) A ga Dc'.sympl Dc.sympl hx hself hUn hpv hrow
    obtain ⟨κ, hκn, hκ⟩ := hall _ hxm (hun hunit) _ A' θ (hMk' _ hMk) (hRd' θ hRd) (hMn' θ hMn)
    refine ⟨κ, hκn, fun i => ?_⟩
    have hev := hκ i.1.1 i.2.1 i.1.2.1 i.2.2.1 i.1.2.2.1.1 i.1.2.2.1.2 i.1.2.2.2.1 i.2.2.2
    have hrd : rdU U i.1.2.2.2.1 k x = evR Xo c i.1.2.2.2.1 (unC U k ⟨x, hx⟩) := by
      simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
      rfl
    simp only [R, T]
    rw [hrd]
    exact hev.trans (_root_.mul_assoc _ _ _)
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Jx R T ρ hρ hol unit
  refine ⟨C, hC0, fun Λ hΛ N hN P hP f hf hsr x hx => ?_⟩
  have hx' := hC ⟨(Λ, N, ⟨P, hP⟩, ⟨f, hf⟩), hΛ, hN, hsr⟩ x hx
  simp only [R, T] at hx'
  rw [hx', _root_.mul_assoc]
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.hermitianThetaLevelData_forms_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → IsSystem X bas idx M D.grp D.lats (D.phi bas hn v₀) μ := by
  first | exact @GlobalTheory.SW.isSystem_level | exact GlobalTheory.SW.isSystem_level | (intros; apply GlobalTheory.SW.isSystem_level <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.cuspForm_frame_readings_linearIndependent : ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  first | exact @GlobalTheory.Dict.readings_independent | exact GlobalTheory.Dict.readings_independent | (intros; apply GlobalTheory.Dict.readings_independent <;> assumption)
end
