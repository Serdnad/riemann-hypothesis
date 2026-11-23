module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.CoordFamily

open Filter Topology GlobalTheory.Specialise GlobalTheory.AmpleSpan GlobalTheory.HolHom

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {I : Type} {t : I → LB.Sec H}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {x : V → (Sp ℂ ⟶ X)} {cf : I → V → ℂ}

theorem eq_of_proportional (ht : EmbedsBy f t) {p p' : Sp ℂ ⟶ X} (hf : p ≫ f = p' ≫ f) {c c' : I → ℂ}
    (h : HasCoords p t c) (h' : HasCoords p' t c') {ρ : ℂ} (e : ∀ i, c' i = ρ * c i) : p = p' := by
  obtain ⟨m, hm⟩ := h'.exists_isUnit ht.1
  have hρ : IsUnit ρ := isUnit_of_mul_isUnit_left (e m ▸ hm)
  have h₁ := h.mul_unit hρ
  have e' : (fun l => c l * ρ) = c' := funext fun l => by rw [e, mul_comm]
  rw [e'] at h₁
  exact h₁.ext ht hf h' hm

theorem holAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z) : HolAt x z := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit ht.1
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hne : ∀ᶠ v in 𝓝 z, cf m v ≠ 0 := (hd m).continuousAt.eventually_ne hm.ne_zero
  have hev : ∀ᶠ v in 𝓝 z, ⊤ ≤ x v ⁻¹ᵁ Out.nonzeroLocus (t m) :=
    hne.mono fun v hv => (hc v).le_nonzeroLocus hv.isUnit
  refine holAt_of_affine hD hev.self_of_nhds hev fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine (differentiableAt_const (valR y ⊤ a)).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [MvPolynomial.eval₂Hom_C, valAt'_eq_valR]
    exact (HolHom.valR_appLE (x v) f ⊤ _ le_top a hv).trans (by rw [hy])
  | add p q hp hq =>
    refine (hp.add hq).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [valAt'_eq_valR, HolHom.valR_eq _ _ hv, map_add (f := _), Pi.add_apply]
  | mul_X p l hp =>
    refine (hp.mul ((hd l).fun_mul ((hd m).fun_inv hm.ne_zero))).congr_of_eventuallyEq
      ((hev.and hne).mono fun v hv => ?_)
    have e := (hc v).valR_ratio hv.1 (hρ l)
    have e' : valR (x v) _ (ρ l) = cf l v * (cf m v)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hv.2]
    simp only [valAt'_eq_valR, map_mul, MvPolynomial.eval₂Hom_X', Pi.mul_apply]
    rw [← e']
    simp only [HolHom.valR_eq _ _ hv.1, map_mul]

theorem hasCoords_deriv (hcov : ⨆ l, Out.nonzeroLocus (t l) = ⊤) (hc : ∀ v, HasCoords (x v) t fun i => cf i v)
    {z w : V} (hx : HolAt x z) (hd : ∀ i, DifferentiableAt ℂ (cf i) z) {ν : Sp (DualNumber ℂ) ⟶ X}
    (hν : IsDerivAt x z w ν) :
    HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w) := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit hcov
  choose ρ hρ using fun l => exists_isRatio (t l) (t m)
  have hz := (hc z).le_nonzeroLocus hm
  have hν' := (le_preimage_dual_iff hν.1 _).2 hz
  have hu : IsUnit (TrivSqZeroExt.inl (cf m z) + TrivSqZeroExt.inr (fderiv ℂ (cf m) z w) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by simpa using hm)
  have h₁ := (hasCoords_ratio hν' hρ).mul_unit hu
  convert h₁ using 2 with l
  have hev : cf l =ᶠ[𝓝 z] fun v => valAt' (x v) _ (ρ l) * cf m v :=
    (hx _ hz).1.mono fun v hv => ((hc v).valR_ratio hv (hρ l)).symm
  have h0 := hev.self_of_nhds
  beta_reduce at h0
  rw [hev.fderiv_eq, h0, fderiv_fun_mul ((hx _ hz).2 _) (hd m)]
  ext
  · simp [fst_valR hν.1 hz]
  · simp [fst_valR hν.1 hz, hν.2 _ hz, mul_comm]

theorem isDerivAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z w : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z)
    {ν : Sp (DualNumber ℂ) ⟶ X} (hb : ν ≫ f = constVec y)
    (hν : HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w)) :
    IsDerivAt x z w ν := by
  have hx := holAt_of_coords ht hy hc hd
  obtain ⟨ν', hν'⟩ := hx.exists_isDerivAt w
  have h1 := hν'.comp f
  have h2 : (fun v => x v ≫ f) = fun _ => y := funext hy
  have h3 : ν' ≫ f = constVec y := (h2 ▸ h1).unique (isDerivAt_const y z w)
  rw [hν.ext_of_isLocalRing ht (hb.trans h3.symm) (hasCoords_deriv ht.1 hc hx hd hν')]
  exact hν'

theorem hasCoords_powOver {S : Scheme.{0}} {G : Over S} {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {b : I → LB.Sec (Out.powOver G L U N)} {A : Type} [CommRing A] [IsLocalRing A]
    {p : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme} {c : I → A}
    (h : ∀ j, ⊤ ≤ (p ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : Aˣ,
      ∀ i, valR p ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = c i * u) : HasCoords p b c := by
  obtain ⟨j, hj⟩ := Points.exists_le_preimage_of_iSup_eq_top (p ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact ⟨fun _ => j, fun s hs => Set.mem_iInter.2 fun _ => hj hs, h j hj⟩

end GlobalTheory.CoordFamily

namespace GlobalTheory


open Specialise HolHom CoordFamily in
theorem coords_determine_family : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (x : V → (Sp ℂ ⟶ (G.hom ⁻¹ᵁ U).toScheme)) (cf : Fin n → V → ℂ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → (∀ v, x v ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y) → (∀ v j, ⊤ ≤ (x v ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : ℂ, u ≠ 0 ∧ ∀ i, valR (x v) ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = cf i v * u) → (∀ v v' (ρ : ℂ), (∀ i, cf i v' = ρ * cf i v) → x v' = x v) ∧ ((∀ i, Differentiable ℂ (cf i)) → IsHolTo Set.univ (fun v => x v ≫ (G.hom ⁻¹ᵁ U).ι) ∧ ∀ (z₀ : V) (ν : Sp (DualNumber ℂ) ⟶ (G.hom ⁻¹ᵁ U).toScheme), ν ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y → (∀ j, ⊤ ≤ (ν ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : (DualNumber ℂ)ˣ, ∀ i, valR ν ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = (TrivSqZeroExt.inl (cf i 0) + TrivSqZeroExt.inr (fderiv ℂ (cf i) 0 z₀)) * (u : DualNumber ℂ)) → ∀ (W : G.left.Opens) (f : Γ(G.left, W)), spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν = x 0 ∧ (⊤ ≤ (x 0 ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (ν ≫ (G.hom ⁻¹ᵁ U).ι) W f) = fderiv ℂ (fun v => valAt' (x v ≫ (G.hom ⁻¹ᵁ U).ι) W f) 0 z₀)) := by
  intro S G _ L U N n b y V _ _ x cf hL _ hb hy hc
  have hc' : ∀ v, HasCoords (x v) b fun i => cf i v := fun v => hasCoords_powOver hL fun j hj => by
    obtain ⟨u, hu, e⟩ := hc v j hj
    exact ⟨Units.mk0 u hu, e⟩
  have hi : (G.hom ∣_ U) ≫ U.ι = (G.hom ⁻¹ᵁ U).ι ≫ G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (G.hom ∣_ U) = x 0 ≫ (G.hom ∣_ U) := fun v => by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hi, hy, hy]
  refine ⟨fun v v' ρ e => (eq_of_proportional hb ((hy' v).trans (hy' v').symm) (hc' v) (hc' v') e).symm,
    fun hd => ⟨isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_coords hb hy' hc' fun i => hd i z).comp _,
      fun z₀ ν hν hνc W f => ?_⟩⟩
  have h := isDerivAt_of_coords (w := z₀) hb hy' hc' (fun i => hd i 0) (ν := ν)
    (by rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hi, hν, hy])
    (hasCoords_powOver hL hνc)
  exact ⟨h.1, fun hW => (h.comp (G.hom ⁻¹ᵁ U).ι).2 W hW f⟩

end GlobalTheory
end
end

section

noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

open NumberField GlobalTheory.TorusExt

section Qk

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

def IsPullQk (hD : IsPullDeg φ D D') {k : ℕ} (p : QkPt D (FractionRing R) k) (p' : QkPt D' (FractionRing R') k) : Prop :=
  ∃ _ : Algebra (FractionRing R) (FractionRing R'), Compat φ (FractionRing R') ∧
    ∃ q : QkPt D (FractionRing R') k, QkExt (algebraMap (FractionRing R) (FractionRing R')) p q ∧
      p'.y = hD.xe.symm q.y ∧ IsPullGtF φ hD (FractionRing R') q.g p'.g

theorem IsPullQk.ext {hD : IsPullDeg φ D D'} {k : ℕ} {p : QkPt D (FractionRing R) k} {p' : QkPt D' (FractionRing R') k}
    (h : IsPullQk hD p p') {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : Compat φ F) {q : QkPt D F k} {q' : QkPt D' F k} (hq : QkExt (algebraMap _ F) p q)
    (hq' : QkExt (algebraMap _ F) p' q') : q'.y = hD.xe.symm q.y ∧ IsPullGtF φ hD F q.g q'.g := by
  obtain ⟨_, hK, q₀, e₀, hy, hg⟩ := h
  have hc : (algebraMap (FractionRing R') F).comp (algebraMap (FractionRing R) (FractionRing R')) =
      algebraMap (FractionRing R) F := IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
    (congrArg (algebraMap (FractionRing R') F) (hK r)).trans (hF r).symm)
  have hs : spMap (algebraMap (FractionRing R) F) =
      spMap (algebraMap (FractionRing R') F) ≫ spMap (algebraMap (FractionRing R) (FractionRing R')) := by
    rw [← hc, spMap_comp]
  have e₁ : QkExt (algebraMap (FractionRing R') F) q₀ q := by
    refine ⟨hq.1.trans e₀.1.symm, ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [hq.2.1, e₀.2.1, hs, Category.assoc]
    · refine (val_corr hJ (hq.2.2 χ) _).trans ((val_pull hJ _ _ _).trans (Eq.trans ?_
        ((val_pull hJ _ _ _).trans ((val_corr hJ (e₀.2.2 χ) _).trans (val_pull hJ _ _ _))).symm))
      exact congrArg (fun r => val (p.g.s χ) r y J) ((congrArg (𝟙 _ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  exact ⟨by rw [hq'.1, hy, e₁.1], isPullGtF_ext hD hF _ (RingHom.comp_id _) hg e₁ hq'⟩

theorem exists_isPullQk (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (hB : D.TauBimult)
    {k : ℕ} (p : QkPt D (FractionRing R) k) : ∃ p', IsPullQk hD p p' := by
  letI : Algebra (FractionRing R) (FractionRing R') := (fracMap hφ).toAlgebra
  have hK : Compat φ (FractionRing R') := fracMap_algebraMap hφ
  have hB' := TauPull.tauBimult_pull hG hD hB
  obtain ⟨q, hq, -⟩ := existsUnique_qkExt (F' := FractionRing R') hB (algebraMap (FractionRing R) (FractionRing R'))
    (RingHom.comp_id _) p
  exact ⟨pullQk hD hG hK hB hB' q, _, hK, q, hq, rfl, isPullGtF_pullGt hD hG hK _⟩

end Qk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def pullTate (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D₀ : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D₀ D') [Module (𝓞 E) D₀.X] [Module (𝓞 E) D'.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {oa' : letI := H.starRing; D'.OAct (𝓞 E)}
    (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y)
    (ho : letI := H.starRing; ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)
    (hB : D₀.TauBimult) (hB' : D'.TauBimult) {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] (hF : Compat φ F) (I : TateIsoQ D D₀ oa F) : TateIsoQ D D' oa' F :=
  letI := H.starRing
  { ζ := I.ζ
    ζ_prim := I.ζ_prim
    ζ_pow := I.ζ_pow
    ev := fun n a => pullQk hD hG hF hB hB' (I.ev n a)
    add := fun n hn a b => qkAdd_pullQk hD hG hF hB hB' (I.add n hn a b)
    lin := fun n hn x a => qkAct_pullQk hD hG hF hB hB' hx ho (I.lin n hn x a)
    ker := fun n hn a b => (equiv_pullQk hD hG hF hB hB' _ _).trans (I.ker n hn a b)
    onto := fun n hn p' => by
      obtain ⟨p, rfl⟩ := pullQk_surjective hD hG hF hB hB' p'
      obtain ⟨a, ha⟩ := I.onto n hn p
      exact ⟨a, (equiv_pullQk hD hG hF hB hB' _ _).2 ha⟩
    tower := fun n m hn hm a => by
      obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm a
      exact ⟨pullQk hD hG hF hB hB' q, congrArg hD.xe.symm h₁, isNsmul_pullGt hD hG hF h₂,
        (equiv_pullQk hD hG hF hB hB' _ _).2 h₃⟩
    isom := fun n hn a b => weilQkIs_pull hD hF rfl (isPullGtF_pullGt hD hG hF _) rfl (isPullGtF_pullGt hD hG hF _)
      (I.isom n hn a b) }

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' O'' : Type} [CommRing O'] [IsDomain O']
  [CommRing O''] [IsDomain O''] {b : O →+* O'}

structure IsBC (f : O' →+* O'') (a : ArcIn D l β O' b) (a' : ArcIn D l β O'' (f.comp b))
    (hD : IsPullDeg f a.D₀ a'.D₀) : Prop where
  xe_smul : ∀ (x : 𝓞 E) (y : a'.D₀.X), hD.xe (x • y) = x • hD.xe y
  be_eq : ∀ y z : a'.D₀.X, a'.be y z = a.be (hD.xe y) (hD.xe z)
  act : letI := H.starRing
    ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst a.D₀.P.A.hom (specOf f) =
      (hD.e.hom.left ≫ pullback.fst a.D₀.P.A.hom (specOf f)) ≫ (a.oa.onB.act x).left
  eta : ∀ v, IsPullQk hD (a.eta v) (a'.eta v)
  etaA : ∀ v, IsPullQk hD (a.etaA v) (a'.etaA v)

def IsBC.xeL {f : O' →+* O''} {a : ArcIn D l β O' b} {a' : ArcIn D l β O'' (f.comp b)} {hD : IsPullDeg f a.D₀ a'.D₀}
    (h : IsBC f a a' hD) : a'.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { hD.xe with map_smul' := h.xe_smul }

variable (hG : GlobalFnsSt) {f : O' →+* O''} (hf : Function.Injective f) (a : ArcIn D l β O' b) {D' : DegPre O''}
  (hD : IsPullDeg f a.D₀ D')

@[reducible] def pullModule : Module (𝓞 E) D'.X := hD.xe.module (𝓞 E)

theorem pullModule_smul (x : 𝓞 E) (y : D'.X) : letI := pullModule a hD; hD.xe (x • y) = x • hD.xe y :=
  hD.xe.apply_symm_apply _

def pullArc : ArcIn D l β O'' (f.comp b) :=
  letI := H.starRing
  letI := pullModule a hD
  have hx := pullModule_smul a hD
  have hB' := TauPull.tauBimult_pull hG hD a.bimult
  have ho := (exists_oAct hD hG hf a.oa hx).choose_spec
  { D₀ := D'
    mod := pullModule a hD
    oa := (exists_oAct hD hG hf a.oa hx).choose
    nontriv := have := a.nontriv; hD.xe.toEquiv.nontrivial
    even := PsiEvenPull.psiEven_pull hG _ _ f _ _ hD a.even
    bimult := hB'
    gen := fun y => psiUnitOn_pull hD hf y (a.gen _)
    w0 := traceFormTwistIso_of_pullback hD hf hx ho a.w0
    be := a.be.comp hD.xe.toAddMonoidHom.toIntLinearMap hD.xe.toAddMonoidHom.toIntLinearMap
    be_symm := fun y z => a.be_symm (hD.xe y) (hD.xe z)
    be_pos := fun y hy => a.be_pos (hD.xe y) (hD.xe.map_ne_zero_iff.2 hy)
    be_adj := fun x y z => by
      show a.be (hD.xe (x • y)) (hD.xe z) = a.be (hD.xe y) (hD.xe (H.bar x • z))
      rw [hx, hx, a.be_adj]
    be_dvd := fun y z => a.be_dvd (hD.xe y) (hD.xe z)
    eta := fun v => (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose
    etaA := fun v => (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose
    geom := fun F _ _ _ r z hr hz f' hf' => by
      letI : Algebra (FractionRing O') F := ((algebraMap (FractionRing O'') F).comp (fracMap hf)).toAlgebra
      have hF : Compat f F := fun x => congrArg (algebraMap (FractionRing O'') F) (fracMap_algebraMap hf x)
      obtain ⟨h₁, I, h₂, h₃, h₄⟩ := a.geom F r z hr hz (f'.comp f) (RingHom.ext fun x => by
        rw [hf']; exact (hF x).symm)
      have lev : ∀ {k : ℕ} (p : QkPt a.D₀ (FractionRing O') k) (p' : QkPt D' (FractionRing O'') k) (e : QkPt a.D₀ F k),
          IsPullQk hD p p' → (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv a.D₀ F q e) →
          ∀ q', QkExt (algebraMap _ F) p' q' → QkPt.Equiv D' F q' (pullQk hD hG hF a.bimult hB' e) := by
        intro k p p' e hp he q' hq'
        obtain ⟨q, hq, -⟩ := existsUnique_qkExt (F' := F) a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) p
        rw [(eq_pullQk_iff hD hG hF a.bimult hB' q q').2 (hp.ext hF hq hq'), equiv_pullQk]
        exact he q hq
      refine ⟨fun τ => ?_, pullTate hG hD hx ho a.bimult hB' hF I, h₂,
        fun v => lev _ _ _ (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose_spec (h₃ v),
        fun v hv => lev _ _ _ (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose_spec (h₄ v hv)⟩
      obtain ⟨n, hn, hn'⟩ := h₁ τ
      refine ⟨n, (LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct a.oa.onB.toRingAct) _ (pull_grp hD) ho F _ τ n).2 ?_, ?_⟩
      · rw [← spMap_comp]; exact hn
      · rw [(({ hD.xe with map_smul' := hx } : D'.X ≃ₗ[𝓞 E] a.D₀.X)).finrank_eq]
        exact hn' }

theorem isBC_pullArc : IsBC f a (pullArc hG hf a hD) hD :=
  letI := H.starRing
  letI := pullModule a hD
  { xe_smul := pullModule_smul a hD
    be_eq := fun _ _ => rfl
    act := (exists_oAct hD hG hf a.oa (pullModule_smul a hD)).choose_spec
    eta := fun v => (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose_spec
    etaA := fun v => (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose_spec }

theorem exists_isBC (hP : PolBaseChangeSt) (hG : GlobalFnsSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' O'' : Type}
    [CommRing O'] [IsDomain O'] [CommRing O''] [IsDomain O''] {b : O →+* O'} (a : ArcIn D l β O' b) (f : O' →+* O'')
    (hf : Function.Injective f) :
    ∃ (a' : ArcIn D l β O'' (f.comp b)) (hD : IsPullDeg f a.D₀ a'.D₀), IsBC f a a' hD ∧ a'.D₀.P.g = a.D₀.P.g := by
  obtain ⟨D', hD, -, hg⟩ := DegPull.exists_isPullDeg hP O' O'' f a.D₀ ⊤ (nonempty_psiOn_top _ a.gen) trivial
  exact ⟨pullArc hG hf a hD, hD, isBC_pullArc hG hf a hD, hg⟩

end GlobalTheory.ArcPull
end
end
