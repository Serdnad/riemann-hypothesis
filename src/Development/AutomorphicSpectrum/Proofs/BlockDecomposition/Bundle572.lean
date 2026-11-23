module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle563
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle565
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle564
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.FirstChernClassFactorial

theorem pow_dvd_factorial_mul (l : ℕ) (hl : 0 < l) (n : ℕ) : l ^ n ∣ (l * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (l * n).factorial * l.factorial ∣ (l * n + l).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add _ _
    have h2 : l ∣ l.factorial := Nat.dvd_factorial hl le_rfl
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih h2).trans h1

theorem factorial_acr {l : ℕ} [Fact l.Prime] (n k : ℕ) (hk : l * n ≤ k) : (k.factorial : (PAlg.base l).Acr n) = 0 := by
  obtain ⟨a, ha⟩ := (pow_dvd_factorial_mul l (Fact.out : l.Prime).pos n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, Nat.cast_mul, Nat.cast_pow, (PAlg.base l).pow_l_acr n, zero_mul]

theorem dlog_eq_of_factorial {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {N N' : ℕ} (h : N ≤ N')
    (hf : ∀ k, N ≤ k → (k.factorial : A) = 0) (v : A) : B.dlog δ N' v = B.dlog δ N v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  rw [hf k (by simpa using hk)]
  simp


open B in
theorem isFirstChern_base_change {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b b' : Base}
    {ht : b.t = 1} {ht' : b'.t = 1} {κ : O →+* b.R ⧸ b.I} {κ' : O →+* b'.R ⧸ b'.I}
    (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (τ : b.R ⧸ b.I →+* b'.R ⧸ b'.I)
    (hτ : τ.comp κ = κ') (hτσ : ∀ r, τ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (σ r))
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (c' : Λ →+* b'.R) (hc : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    (D : E.LineData X) {N N' : ℕ} (hN : N ≤ N') (hf : ∀ k, N ≤ k → (k.factorial : b'.R) = 0)
    (y : CH.H (OM ((schFn q).cr b ht κ) c) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N' y) :
    IsFirstChernClassOfLineBundle (q := q) (b := b') (ht := ht') (κ := κ') D c' N
      ((omMor (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc).pull 2 y) := by
  intro C _ G Lf
  let mm := omMor (c := c) (c' := c') (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc
  let G' : C ⥤ Thick ((schFn q).cr b ht κ) := G ⋙ mm.G
  let Lf' : CLift G' D := { p := Lf.p, hp := Lf.hp, w := Lf.w, hw := Lf.hw }
  obtain ⟨hz', hcl⟩ := hy C G' Lf'
  let m4 : CH.Mor (G' ⋙ OM _ c) (G ⋙ OM _ c') (RingHom.id _) :=
    { G := 𝟭 C, τ := fun T => mm.τ (G.obj T), nat := fun φ x => mm.nat (G.map φ) x }
  have hE : m4.pullC 2 (Lf'.coc c N') = Lf.coc c' N := by
    funext s
    refine dlog_eq_of_factorial (G.obj (s.obj (Fin.last 2))).δ hN (fun j hj => ?_) _
    have := congrArg (G.obj (s.obj (Fin.last 2))).i (hf j hj)
    rw [map_natCast, map_zero] at this
    exact this
  have hz : CH.d _ 2 (Lf.coc c' N) = 0 := by
    rw [← hE, m4.d_pullC, hz', map_zero]
  refine ⟨hz, ?_⟩
  have h1 : (CH.Mor.restrict (OM _ c') G).pull 2 (mm.pull 2 y) =
      m4.pull 2 ((CH.Mor.restrict (OM _ c) G').pull 2 y) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  refine Eq.trans ?_ h1.symm
  rw [← hcl]
  have key : ∀ (z : CH.Cn (G ⋙ OM _ c') 2) (h : CH.d _ 2 z = 0), z = Lf.coc c' N →
      (CH.cx _).cls z h = (CH.cx _).cls (Lf.coc c' N) hz := by
    rintro _ _ rfl
    rfl
  exact (key (m4.pullC 2 (Lf'.coc c N')) (by rw [m4.d_pullC, hz', map_zero]) hE).symm


open B in
theorem chern_class_reduction_compatible {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (k : Bool)
    (D : E.LineData X) (n : ℕ) (y : B.Hc (schFn q) κ k (n + 1) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := bs l k (n + 1)) (ht := rfl) (κ := κb κ k (n + 1)) D ((PAlg.base l).cris (n + 1)) (l * (n + 1)) y) :
    IsFirstChernClassOfLineBundle (q := q) (b := bs l k n) (ht := rfl) (κ := κb κ k n) D ((PAlg.base l).cris n) (l * n)
      (redHc (schFn q) κ k n.le_succ 2 y) :=
  isFirstChern_base_change (b := bs l k (n + 1)) (b' := bs l k n) ((PAlg.base l).red n.le_succ) rfl (dd_red k _ n.le_succ)
    (Ideal.quotientMap _ _ (red_le k n.le_succ)) (red_κb κ k n.le_succ) (fun _ => rfl) _ _ (red_cris _ n.le_succ) D
    (Nat.mul_le_mul_left l n.le_succ) (fun j hj => factorial_acr n j hj) y hy

theorem exists_C1H {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (D : E.LineData M.X)
    (hD : sSup (𝒱D D) = ⊤) : ∃ x : (M.HS false 2).lim, B.IsFirstChernFamily M.p D (okToOC l K) false x.1 := by
  have ex : ∀ n, ∃! x, B.IsFirstChernClassOfLineBundle (q := M.p) (b := B.bs l false n) (ht := rfl) (κ := B.κb (okToOC l K) false n) D
      ((PAlg.base l).cris n) (l * n) x := fun n =>
    GlobalTheory.T.existsUnique_chern_class_nilpotent_base (B.DD false (PAlg.base l) n) l (Fact.out : l.Prime).ne_zero M.p (B.κb (okToOC l K) false n) D hD
      ((PAlg.base l).cris n) (l * n) (factorial_acr n _ le_rfl)
  choose x hx hu using ex
  refine ⟨⟨x, fun n => ?_⟩, hx⟩
  exact hu n _ (chern_class_reduction_compatible M.p (okToOC l K) false D n (x (n + 1)) (hx (n + 1)))

end GlobalTheory.CompanionTheory.FirstChernClassFactorial
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.teichmuller_nu_galois_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) = galM r M σ hσ n j (Mid.nu r M n j hT x) := by
  first | exact @GlobalTheory.CompanionTheory.NuGalSquare.nu_gal | exact GlobalTheory.CompanionTheory.NuGalSquare.nu_gal | (intros; apply GlobalTheory.CompanionTheory.NuGalSquare.nu_gal <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.teichmuller_nu_pullback_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (n j : ℕ) (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by
  first | exact @GlobalTheory.CompanionTheory.NuPull.nu_pull | exact GlobalTheory.CompanionTheory.NuPull.nu_pull | (intros; apply GlobalTheory.CompanionTheory.NuPull.nu_pull <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.teichmuller_nu_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j), (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) = Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  first | exact @GlobalTheory.CompanionTheory.NuRed.nu_red | exact GlobalTheory.CompanionTheory.NuRed.nu_red | (intros; apply GlobalTheory.CompanionTheory.NuRed.nu_red <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_comparison_frobenius_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M n), phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by
  first | exact @GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | exact GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | (intros; apply GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_comparison_pullback_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n), pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by
  first | exact @GlobalTheory.CompanionTheory.CrisBase.pullM_bW | exact GlobalTheory.CompanionTheory.CrisBase.pullM_bW | (intros; apply GlobalTheory.CompanionTheory.CrisBase.pullM_bW <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_comparison_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)), (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) := by
  first | exact @GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | exact GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | (intros; apply GlobalTheory.CompanionTheory.CrisBaseChange.bW_red <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_comparison_galois_fixed : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (y : (HSW r M j).M n), galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by
  first | exact @GlobalTheory.CompanionTheory.BWGal.bW_gal | exact GlobalTheory.CompanionTheory.BWGal.bW_gal | (intros; apply GlobalTheory.CompanionTheory.BWGal.bW_gal <;> assumption)
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.ChartRed

theorem etale_of_quot {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] (f : R →+* S)
    (hf : f.Etale) (g : R →+* R') (hg : Function.Surjective g) (h : S →+* S') (hh : Function.Surjective h)
    (f' : R' →+* S') (comm : f'.comp g = h.comp f) (hk : RingHom.ker h = (RingHom.ker g).map f) : f'.Etale := by
  letI := f.toAlgebra
  haveI : Algebra.Etale R S := hf
  set P := RingHom.ker g with hP
  have het : Algebra.Etale (R ⧸ P) (S ⧸ P.map (algebraMap R S)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S P).symm
  have h0 : (algebraMap (R ⧸ P) (S ⧸ P.map (algebraMap R S))).Etale := RingHom.etale_algebraMap.2 het
  let e1 : (R ⧸ P) ≃+* R' := RingHom.quotientKerEquivOfSurjective hg
  let e2 : (S ⧸ P.map (algebraMap R S)) ≃+* S' :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hh)
  have key : f' = (e2.toRingHom.comp (algebraMap (R ⧸ P) (S ⧸ P.map (algebraMap R S)))).comp e1.symm.toRingHom := by
    refine RingHom.ext fun r' => ?_
    obtain ⟨r, rfl⟩ := hg r'
    have h1 : e1.symm (g r) = Ideal.Quotient.mk P r := by
      rw [RingEquiv.symm_apply_eq]; rfl
    have h2 : f' (g r) = h (f r) := RingHom.congr_fun comm r
    change _ = e2 (algebraMap _ _ (e1.symm (g r)))
    rw [h1, h2]
    rfl
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e1.symm.bijective)
    (RingHom.Etale.stableUnderComposition _ _ h0 (RingHom.Etale.of_bijective e2.bijective))

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l]

theorem ker_red (n : ℕ) : RingHom.ker (Wc.red l k n) =
    Ideal.span {(Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ (n + 1)}) ((l : WittVector l k) ^ n))} := by
  unfold Wc.red
  rw [Ideal.Quotient.factor_ker, Ideal.map_span, Set.image_singleton]

theorem red_surj (n : ℕ) : Function.Surjective (Wc.red l k n) :=
  Ideal.Quotient.factor_surjective _

theorem map_Im (n : ℕ) : (Wc.Im l k (n + 1)).map (Wc.red l k n) = Wc.Im l k n := by
  unfold Wc.Im
  rw [Ideal.map_map]
  rfl

variable {O : Type} [CommRing O] {F : B.Fn O} {ρ : O →+* k} {n : ℕ}

theorem etale_q (T : Thick (Wc.L l F ρ (n + 1))) {d : ℕ} (t : Fin d → T.B)
    (h : (MvPolynomial.eval₂Hom T.i t : MvPolynomial (Fin d) (Wc.Wm l k (n + 1)) →+* T.B).Etale) :
    (MvPolynomial.eval₂Hom (qi T) (fun i => Ideal.Quotient.mk (lI n T) (t i)) :
      MvPolynomial (Fin d) (Wc.Wm l k n) →+* T.B ⧸ lI n T).Etale := by
  refine etale_of_quot _ h (MvPolynomial.map (Wc.red l k n)) (MvPolynomial.map_surjective _ (red_surj n))
    (Ideal.Quotient.mk (lI n T)) Ideal.Quotient.mk_surjective _ ?_ ?_
  · refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [qi_red]
    · simp
  · rw [Ideal.mk_ker, MvPolynomial.ker_map, ker_red, Ideal.map_map, Ideal.map_span, Set.image_singleton]
    simp [lI]

theorem J_q (T : Thick (Wc.L l F ρ (n + 1))) (h : T.J = (Wc.Im l k (n + 1)).map T.i) :
    T.J.map (Ideal.Quotient.mk (lI n T)) = (Wc.Im l k n).map (qi T) := by
  have e : (Ideal.Quotient.mk (lI n T)).comp T.i = (qi T).comp (Wc.red l k n) :=
    RingHom.ext fun r => (qi_red T r).symm
  calc T.J.map (Ideal.Quotient.mk (lI n T))
      = ((Wc.Im l k (n + 1)).map T.i).map (Ideal.Quotient.mk (lI n T)) := by rw [← h]
    _ = (Wc.Im l k (n + 1)).map ((Ideal.Quotient.mk (lI n T)).comp T.i) := Ideal.map_map _ _
    _ = (Wc.Im l k (n + 1)).map ((qi T).comp (Wc.red l k n)) := by rw [e]
    _ = ((Wc.Im l k (n + 1)).map (Wc.red l k n)).map (qi T) := (Ideal.map_map _ _).symm
    _ = (Wc.Im l k n).map (qi T) := by rw [map_Im n]

abbrev rr (n : ℕ) : Wc.Wm l k (n + 1) ⧸ Wc.Im l k (n + 1) →+* Wc.Wm l k n ⧸ Wc.Im l k n :=
  Ideal.quotientMap _ (Wc.red l k n) (Ideal.map_le_iff_le_comap.1 (Wc.dp_red l k n).1)

theorem rr_surj (n : ℕ) : Function.Surjective (rr (l := l) (k := k) n) :=
  Ideal.quotientMap_surjective (red_surj n)

theorem qy_rr (T : Thick (Wc.L l F ρ (n + 1))) : (qy T).comp (rr n) = (qe T).comp T.y.1.1 := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have h := T.w r
  change qy T (rr n (Ideal.Quotient.mk _ r)) = qe T ((Wc.L l F ρ (n + 1)).str T.y (Ideal.Quotient.mk _ r))
  rw [h]
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

theorem qe_bij (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) : Function.Bijective (qe T) := by
  refine ⟨?_, Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : Ideal.Quotient.mk (lI n T) x ∈ T.J.map (Ideal.Quotient.mk (lI n T)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 ha
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (lI_le hn T)] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.2 h1

section Abs

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem map_eq_iff {κ' : Type} [CommRing κ'] {κ : O →+* κ'} {A : CommRingCat.{0}} {C : Type} [CommRing C]
    (φ : C →+* A) (z : PtOver X q κ C) (y : PtOver X q κ A) :
    (ptFun X q κ).map (CommRingCat.ofHom φ) z = y ↔
      φ.comp z.1.1 = y.1.1 ∧ Spec.map (CommRingCat.ofHom φ) ≫ z.1.2 = y.1.2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 h2)

theorem rep_abs {K₁ K₂ C₁ C₂ : Type} [CommRing K₁] [CommRing K₂] [CommRing C₁] [CommRing C₂] {κ₁ : O →+* K₁}
    {κ₂ : O →+* K₂} (r : K₁ →+* K₂) (hr : Function.Surjective r) (hκ : r.comp κ₁ = κ₂) (e : C₁ →+* C₂)
    (he : Function.Bijective e) (z₁ : PtOver X q κ₁ C₁) (z₂ : PtOver X q κ₂ C₂) (h1 : z₂.1.1.comp r = e.comp z₁.1.1)
    (h2 : z₂.1.2 = Spec.map (CommRingCat.ofHom e) ≫ z₁.1.2) {V : X.Opens}
    (hrep : ∀ (A : CommRingCat.{0}) (y : PtOver X q κ₁ A), ⊤ ≤ y.1.2 ⁻¹ᵁ V →
      ∃! φ : C₁ →+* A, (ptFun X q κ₁).map (CommRingCat.ofHom φ) z₁ = y)
    (A : CommRingCat.{0}) (y : PtOver X q κ₂ A) (hy : ⊤ ≤ y.1.2 ⁻¹ᵁ V) :
    ∃! φ : C₂ →+* A, (ptFun X q κ₂).map (CommRingCat.ofHom φ) z₂ = y := by
  let y' : PtOver X q κ₁ A := ⟨(y.1.1.comp r, y.1.2), by
    have h := y.2
    rw [RingHom.comp_assoc, hκ]
    exact h⟩
  obtain ⟨φ', h', hu⟩ := hrep A y' hy
  rw [map_eq_iff] at h'
  let E := RingEquiv.ofBijective e he
  have hE : ∀ x, E.symm (e x) = x := fun x => E.symm_apply_apply x
  have hE' : ∀ x, e (E.symm x) = x := fun x => E.apply_symm_apply x
  have hcomp : (φ'.comp E.symm.toRingHom).comp e = φ' := RingHom.ext fun x => by simp [hE]
  have hsp : ∀ ψ : C₂ →+* A, Spec.map (CommRingCat.ofHom ψ) ≫ z₂.1.2 =
      Spec.map (CommRingCat.ofHom (ψ.comp e)) ≫ z₁.1.2 := fun ψ => by
    rw [h2, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨φ'.comp E.symm.toRingHom, ?_, fun ψ hψ => ?_⟩
  · refine (map_eq_iff _ _ _).2 ⟨?_, ?_⟩
    · refine RingHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := hr x
      have e1 : z₂.1.1 (r a) = e (z₁.1.1 a) := RingHom.congr_fun h1 a
      have e2 : φ' (z₁.1.1 a) = y.1.1 (r a) := RingHom.congr_fun h'.1 a
      change φ' (E.symm (z₂.1.1 (r a))) = _
      rw [e1, hE, e2]
    · rw [hsp, hcomp]
      exact h'.2
  · obtain ⟨g1, g2⟩ := (map_eq_iff _ _ _).1 hψ
    have : ψ.comp e = φ' := by
      refine hu _ ((map_eq_iff _ _ _).2 ⟨?_, ?_⟩)
      · refine RingHom.ext fun a => ?_
        have e1 : z₂.1.1 (r a) = e (z₁.1.1 a) := RingHom.congr_fun h1 a
        have e2 : ψ (z₂.1.1 (r a)) = y.1.1 (r a) := RingHom.congr_fun g1 (r a)
        change ψ (e (z₁.1.1 a)) = y.1.1 (r a)
        rw [← e1, e2]
      · rw [← hsp]
        exact g2
    rw [← this]
    refine RingHom.ext fun x => ?_
    change ψ x = ψ (e (E.symm x))
    rw [hE']

end Abs

abbrev tD {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ρ : O →+* k} {m : ℕ} {W : X.Opens}
    {d : ℕ} (c' : Chart (Wc.pd l k m) l q ((Wc.res l k m).comp ρ) W d) : Thick (Wc.L l (B.schFn q) ρ m) := c'.D

def cq {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ}
    (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d) :
    Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d where
  D := qT (F := B.schFn q) (ρ := ρ) hn (tD c')
  t := fun i => Ideal.Quotient.mk (lI n (tD c')) (c'.t i)
  etale := etale_q (tD c') c'.t c'.etale
  J_eq := J_q (tD c') c'.J_eq
  inV := inU_qT q ρ hn (tD c') c'.inV
  rep := rep_abs (rr n) (rr_surj n) (Wc.red_res l ρ n) (qe (tD c')) (qe_bij hn (tD c')) (tD c').y
    (qT (F := B.schFn q) (ρ := ρ) hn (tD c')).y (qy_rr (tD c')) rfl c'.rep

theorem chart_q {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ}
    (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d) :
    ∃ (c : Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d)
      (e : c.D ≅ (qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D),
      (∀ i, e.hom.φ (c.t i) = Ideal.Quotient.mk _ (c'.t i)) ∧
        (FlatT ((qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D) → FlatT c.D) :=
  ⟨cq q ρ hn c', Iso.refl _, fun i => rfl, id⟩

end GlobalTheory.CompanionTheory.ChartRed

end
end

section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralMult

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem finite_range_inter (C : Set (GA E N)) (hC : IsCompact C) :
    (C ∩ ((ratGL E N).range : Set (GA E N))).Finite := by
  have : T2Space (GA E N) := by
    have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
    exact Units.isEmbedding_embedProduct.t2Space
  have : T1Space (GA E N) := T2Space.t1Space
  have hd : DiscreteTopology ((ratGL E N).range) := GlobalTheory.MirTower.discrete_of_le_range le_rfl
  have hcl : IsClosed (((ratGL E N).range : Subgroup (GA E N)) : Set (GA E N)) :=
    Subgroup.isClosed_of_discrete
  have hK : IsCompact (C ∩ ((ratGL E N).range : Set (GA E N))) := hC.inter_right hcl
  have hds : DiscreteTopology ↥(C ∩ ((ratGL E N).range : Set (GA E N))) :=
    DiscreteTopology.of_subset hd Set.inter_subset_right
  exact hK.finite ⟨hds⟩

theorem mul_inv_eq_of_central {G : Type} [Group G] {z x a b q r : G} (hz : ∀ g, z * g = g * z)
    (ha : a * x = z * q) (hb : b * x = z * r) : a * b⁻¹ = q * r⁻¹ := by
  have h1 : a = z * q * x⁻¹ := eq_mul_inv_of_mul_eq ha
  have h2 : b = z * r * x⁻¹ := eq_mul_inv_of_mul_eq hb
  have h3 : z * q * x⁻¹ * (z * r * x⁻¹)⁻¹ = z * (q * r⁻¹) * z⁻¹ := by group
  rw [h1, h2, h3, hz, mul_inv_cancel_right]

theorem multC : PositivityTheory.Rg.BcB.E.E3.MultC := by
  intro E _ _ _ N Q hQ
  have hC : IsCompact (Q * Q⁻¹) := hQ.mul hQ.inv
  have hF := finite_range_inter (Q * Q⁻¹) hC
  refine ⟨hF.toFinset.card, fun z hz x => ?_⟩
  rw [← hF.encard_eq_coe_toFinset_card]
  rcases Set.eq_empty_or_nonempty
    {γ : (ratGL E N).range | (γ : GA E N) * x ∈ (fun q => z * q) '' Q} with h0 | ⟨γ₀, q₀, hq₀, e₀⟩
  · rw [h0]
    simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : (ratGL E N).range => (γ : GA E N) * (γ₀ : GA E N)⁻¹) ?_ ?_
    · rintro γ ⟨q, hq, e⟩
      refine ⟨?_, mul_mem γ.2 (inv_mem γ₀.2)⟩
      have e' : (γ : GA E N) * (γ₀ : GA E N)⁻¹ = q * q₀⁻¹ := mul_inv_eq_of_central hz e.symm e₀.symm
      change (γ : GA E N) * (γ₀ : GA E N)⁻¹ ∈ Q * Q⁻¹
      rw [e']
      exact Set.mul_mem_mul hq (Set.inv_mem_inv.2 hq₀)
    · intro γ _ γ' _ h
      exact Subtype.ext (mul_right_cancel h)

end GlobalTheory.CompanionTheory.CentralMult

end
end

section

open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

theorem _root_.GlobalTheory.T.limit_node_embedding : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.NodeEmb := by
  first | exact @GlobalTheory.CompanionTheory.TreeNode.nodeEmb | exact GlobalTheory.CompanionTheory.TreeNode.nodeEmb | (intros; apply GlobalTheory.CompanionTheory.TreeNode.nodeEmb <;> assumption)
end Lim5
end SpectralAccumulation
end BcB
end Rg
end PositivityTheory
end

section

open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

theorem _root_.GlobalTheory.T.limit_twist_bound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  first | exact @GlobalTheory.CompanionTheory.TotalTrace.twBound | exact GlobalTheory.CompanionTheory.TotalTrace.twBound | (intros; apply GlobalTheory.CompanionTheory.TotalTrace.twBound <;> assumption)
end Lim5
end SpectralAccumulation
end BcB
end Rg
end PositivityTheory
end
