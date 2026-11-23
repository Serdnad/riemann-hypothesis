module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle614
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle527
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle633
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
public import Mathlib.FieldTheory.KummerExtension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_OC_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : ℂ_[l]) (c : OC l)
    (h : a ^ N = (c : ℂ_[l])) : a ∈ 𝓞_ℂ_[l] := by
  rw [GlobalTheory.RingBasics.mem_OC]
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 c.2
  rw [← h, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

theorem exists_OC_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] (f : OC l →+* D)
    {N : ℕ} (hN : 0 < N) (c : OC l) (r : D) (h : r ^ N = f c) : ∃ s : OC l, f s = r := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ_[l]) hN
  haveI : NeZero (N : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] N
  let a' : OC l := ⟨a, mem_OC_of_pow_eq hN a c ha⟩
  let ζ' : OC l := ⟨ζ, mem_OC_of_pow_eq hN ζ 1 hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' N :=
    IsPrimitiveRoot.of_map_of_injective (f := (𝓞_ℂ_[l]).subtype) hζ Subtype.val_injective
  have ha' : a' ^ N = c := Subtype.ext ha
  have hp := congrArg (Polynomial.eval₂ f r) (X_pow_sub_C_eq_prod hζ' hN ha')
  rw [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h,
    sub_self, eq_comm, Finset.prod_eq_zero_iff] at hp
  obtain ⟨i, -, hi⟩ := hp
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hi
  exact ⟨_, hi.symm⟩

theorem exists_alg_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : Om l) (s : ℂ_[l])
    (h : s ^ N = (a : ℂ_[l])) : ∃ z : Om l, s = (z : ℂ_[l]) := by
  have hf : (Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hN a
  have hroot : ((Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)).map
      (algebraMap (Om l) ℂ_[l])).IsRoot s := by
    simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [h]
    exact sub_self _
  obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
  exact ⟨z, hz.symm⟩

theorem eq_of_forall_dvd_root_sub {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : O) [IsHausdorff (Ideal.span {c}) O] (v w : O)
    (h : ∀ n : ℕ, c ∣ ((frobeniusEquiv O l).symm)^[n] v - ((frobeniusEquiv O l).symm)^[n] w) : v = w := by
  have hp : ∀ (n : ℕ) (x : O), (((frobeniusEquiv O l).symm)^[n] x) ^ (l ^ n) = x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {c}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h1 := pow_dvd_pow_of_dvd (h n) (l ^ n)
  rw [sub_pow_char_pow, hp, hp] at h1
  exact (pow_dvd_pow c (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans h1

theorem exists_gal_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc v hv
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨f, hf, hinj, hdom, hmod⟩ := GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc
  obtain ⟨hprime, hπ⟩ := GlobalTheory.T.breuilKisin_prime_uniformizer_class l K bk
  obtain ⟨halg, hfix⟩ := GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk
  set π : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) with hπd
  have hft : ∀ y : OCb l, f y.untilt = Ideal.Quotient.mk _ (WittVector.teichmuller l (ψ y)) := fun y => by
    rw [← WittVector.fontaineTheta_teichmuller, ← WittVector.map_teichmuller]
    exact hf _
  let r : ℕ → WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)} := fun n =>
    Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v))
  have hr0 : r 0 = f bk.flat.untilt := by
    rw [hft]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hv)
  have hrs : ∀ n, r (n + 1) ^ l = r n := fun n => by
    simp only [r]
    rw [← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  have hrn : ∀ n, r n ^ (l ^ n) = f bk.flat.untilt := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_one, hr0]
    | succ n ih => rw [pow_succ', pow_mul, hrs, ih]
  choose s hs using fun n => exists_OC_eq_of_pow_eq f (pow_pos hl n) _ _ (hrn n)
  have hss : ∀ n, s (n + 1) ^ l = s n := fun n => hinj (by rw [map_pow, hs, hs, hrs])
  have hsn : ∀ n, s n ^ (l ^ n) = bk.flat.untilt := fun n => hinj (by rw [map_pow, hs, hrn])
  have hπc : ((bk.flat.untilt : OC l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← hπ, coe_intToOC]
  have hcoe : Function.Injective (fun z : Om l => (z : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hcp : ∀ (z : Om l) (m : ℕ), ((z ^ m : Om l) : ℂ_[l]) = (z : ℂ_[l]) ^ m :=
    fun z m => map_pow (algebraMap (Om l) ℂ_[l]) z m
  choose z hz using fun n => exists_alg_eq_of_pow_eq (pow_pos hl n) ((π : ↥K.1) : Om l) (s n : ℂ_[l])
    (by rw [← hπc, ← hsn n, SubmonoidClass.coe_pow])
  choose y hy using halg
  have hts : ∀ n, GlobalTheory.MemLoc.rootT bk.flat (n + 1) ^ l = GlobalTheory.MemLoc.rootT bk.flat n := fun n => by
    rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  obtain ⟨g, hg⟩ := GlobalTheory.T.galois_transitive_on_prime_power_root_systems l K π hprime y z
    (hcoe (by
      change ((y 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hy, ← hπc]
      rfl))
    (hcoe (by
      change ((z 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hz, ← hπc, ← hsn 0, pow_zero, pow_one]))
    (fun n => hcoe (by
      change ((y (n + 1) ^ l : Om l) : ℂ_[l]) = ((y n : Om l) : ℂ_[l])
      rw [hcp, ← hy, ← hy, ← hts n, SubmonoidClass.coe_pow]))
    (fun n => hcoe (by
      change ((z (n + 1) ^ l : Om l) : ℂ_[l]) = ((z n : Om l) : ℂ_[l])
      rw [hcp, ← hz, ← hz, ← hss n, SubmonoidClass.coe_pow]))
  obtain ⟨w, hw⟩ := GlobalTheory.tilt_of_compatible_roots l s hss
  have hgw : Per.σF (g : GQ l) bk.flat = w := hfix _ _ fun n => Subtype.ext (by
    refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
    rw [hy, hw, hz, ← hg n]
    exact GlobalTheory.RingBasics.σC_coe _ _)
  refine ⟨g, ?_⟩
  rw [hgw]
  refine eq_of_forall_dvd_root_sub (l := l) (ψ bk.flat) v (ψ w) fun n => ?_
  have hψ : ∀ m, ψ (((frobeniusEquiv (OCb l) l).symm)^[m] w) = ((frobeniusEquiv O l).symm)^[m] (ψ w) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, RingHom.map_frobeniusEquiv_symm]
  have h1 := hft (((frobeniusEquiv (OCb l) l).symm)^[n] w)
  have h2 : f (s n) = Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w))) := by
    rw [← hw n, ← hψ]
    exact h1
  have h3 := hmod (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v) -
      WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w)))
    (by rw [map_sub, ← h2, hs, sub_self]; exact dvd_zero _)
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h3
  exact (dvd_pow_self _ bk.deg_pos.ne').trans h3

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedF

variable {l : ℕ} [Fact l.Prime]

theorem aw_injective (C : Core l) (a : ℕ) [NeZero a] :
    Function.Injective ((Per.aB l).comp (wA l a).toRingHom) := by
  haveI : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  haveI : Nontrivial (Per.Bcris l) := C.ι.domain_nontrivial
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (((l : ℕ) : Per.Bcris l) ^ m * ((Per.aB l).comp (wA l a).toRingHom) (b : Wq l a)) :=
    ((isUnit_l_Bcris l).pow m).mul (b.isUnit.map _)
  exact hu.ne_zero hx

theorem clear_den {d : ℕ} {R : Type} [CommRing R] (f : R →+* Per.Bcris l)
    (G : Matrix (Fin d) (Fin d) (Per.Bcris l))
    (h : ∀ i j, ∃ (n : ℕ) (w : R), ((l : ℕ) : Per.Bcris l) ^ n * G i j = f w) :
    ∃ (k : ℕ) (F : Matrix (Fin d) (Fin d) R), ((l : ℕ) : Per.Bcris l) ^ k • G = F.map f := by
  choose n w hw using h
  refine ⟨Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2),
    Matrix.of fun i j => ((l : ℕ) : R) ^ (Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) - n i j) * w i j, ?_⟩
  ext i j
  have hle : n i j ≤ Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) :=
    Finset.le_sup (f := fun p : Fin d × Fin d => n p.1 p.2) (Finset.mem_univ (i, j))
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_natCast, smul_eq_mul,
    ← hw]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem inv_entries {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hρ : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l)) = U' * U.map (Per.φB l) ∧
    (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l)) = U'.map (Per.φB l) * U := by
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hR : (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := hρ g
  have hσ1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσU' : U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
    calc U'.map (Per.σB (g : GQ l))
        = (U' * (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) * U'.map (Per.σB (g : GQ l)) := by
          rw [mul_assoc U', hR, hU'U, one_mul]
      _ = U' * (ρ g).map (Per.zB l) := by rw [mul_assoc, hσ1, mul_one]
  have hφR : ((ρ g).map (Per.zB l)).map (Per.φB l) = (ρ g).map (Per.zB l) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.1, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1]
  have hcomm : ∀ M : Matrix (Fin d) (Fin d) (Per.Bcris l),
      (M.map (Per.φB l)).map (Per.σB (g : GQ l)) = (M.map (Per.σB (g : GQ l))).map (Per.φB l) := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact ((ActLaws.act_laws l).2.2.2.2.1 _ _).symm
  constructor
  · calc (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l))
        = U'.map (Per.σB (g : GQ l)) * (U.map (Per.σB (g : GQ l))).map (Per.φB l) := by
          rw [Matrix.map_mul, hcomm]
      _ = U' * (((ρ g).map (Per.zB l)).map (Per.φB l) * (U.map (Per.σB (g : GQ l))).map (Per.φB l)) := by
          rw [hσU', hφR, mul_assoc]
      _ = U' * U.map (Per.φB l) := by rw [← Matrix.map_mul, hR]
  · calc (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l))
        = (U'.map (Per.σB (g : GQ l))).map (Per.φB l) * U.map (Per.σB (g : GQ l)) := by
          rw [Matrix.map_mul, hcomm]
      _ = U'.map (Per.φB l) * ((ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) := by
          rw [hσU', Matrix.map_mul, hφR, mul_assoc]
      _ = U'.map (Per.φB l) * U := by rw [hR]

theorem frob_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) →
    ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)),
      F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧
      (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  intro l _ K bk C hC d ρ U U' hUU hρ
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hent : ∀ G : Matrix (Fin d) (Fin d) (Per.Bcris l), (∀ g : ↥(GK K), G.map (Per.σB (g : GQ l)) = G) →
      ∀ i j, ∃ (n : ℕ) (w : Wq l bk.a),
        ((l : ℕ) : Per.Bcris l) ^ n * G i j = ((Per.aB l).comp (wA l bk.a).toRingHom) w := by
    intro G hG i j
    obtain ⟨x, hxK, hx⟩ := hC K (G i j) fun g hg => by
      have := congrFun (congrFun (hG ⟨g, hg⟩) i) j
      simpa only [Matrix.map_apply] using this
    obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_pow_mul_unramified_eq_witt_bcris l K bk C x hxK
    exact ⟨n, w, by rw [← hx, hw]; rfl⟩
  obtain ⟨k, F, hF⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).1)
  obtain ⟨k', F', hF'⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).2)
  have hGG : (U' * U.map (Per.φB l)) * (U'.map (Per.φB l) * U) = 1 := by
    rw [mul_assoc, ← mul_assoc (U.map _), ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _),
      one_mul, hU'U]
  refine ⟨k, k + k', F, F', ?_, ?_⟩
  · apply Matrix.map_injective (aw_injective C bk.a)
    change (F * F').map ((Per.aB l).comp (wA l bk.a).toRingHom) =
      (((l : ℕ) : Wq l bk.a) ^ (k + k') • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))).map
        ((Per.aB l).comp (wA l bk.a).toRingHom)
    rw [Matrix.map_mul, ← hF, ← hF', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, hGG]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  · rw [← hF, Matrix.mul_smul, ← mul_assoc, hUU, one_mul]

end GlobalTheory.SeedF
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_toDisc_add_le_max (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : A) :
    ‖toDisc l u ρ (a + b)‖ ≤ max ‖toDisc l u ρ a‖ ‖toDisc l u ρ b‖ := by
  have h1 : ∀ c, ‖toDisc l u ρ c‖ = gauge l u ρ (algebraMap A (PreDisc l u ρ) c) := fun c => norm_ofPre l u ρ _
  rewrite [h1, h1, h1, map_add]
  exact gauge_add_le_max l u ρ _ _

theorem norm_hf_g_X_and_φ_le :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
      (f g : Hom bk.prism B),
      ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) g X)‖ ≤ bk.ρ₀ ∧
        ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (B.D.φ (BK.hf (bk := bk) f X))‖ ≤ bk.ρ₀ := by
  intro l _ K bk B f g
  obtain ⟨hρ0, hρ1, hlρ, hE⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk B.A (BK.hf (bk := bk) f)
  have hd : BK.hf (bk := bk) f bk.E ∣ BK.hf (bk := bk) g X - BK.hf (bk := bk) f X := by
    obtain ⟨hfI, hfX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f
    obtain ⟨_, hgX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g
    rw [← Ideal.mem_span_singleton, ← hfI]
    exact Ideal.Quotient.eq.1 (hgX.trans hfX.symm)
  have h : ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f X ^ 1)‖ ≤ (bk.ρ₀ : ℝ) ^ 1 := norm_toDisc_pow_le 1 hρ0
  have hX : ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f X)‖ ≤ bk.ρ₀ := by simpa only [pow_one] using h
  have key : ∀ a b : B.A, ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (a + b)‖ ≤
      max ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ a‖ ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ b‖ :=
    norm_toDisc_add_le_max l (BK.hf (bk := bk) f X) bk.ρ₀
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := hd
    have e : BK.hf (bk := bk) g X = BK.hf (bk := bk) f X + BK.hf (bk := bk) f bk.E * w := eq_add_of_sub_eq' hw
    rewrite [e]
    refine (key _ _).trans (max_le hX ?_)
    rewrite [map_mul]
    refine (norm_mul_le _ _).trans ?_
    calc ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f bk.E)‖ * ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ w‖
        ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hE (norm_toDisc_le w) (norm_nonneg _) (by positivity)
      _ ≤ bk.ρ₀ := (mul_one _).trans_le hlρ
  · have e1 : B.D.φ (BK.hf (bk := bk) f X) = BK.hf (bk := bk) f (frobS l bk.a X) :=
      (Hom.f_φ f (show bk.prism.A from X)).symm
    have e : B.D.φ (BK.hf (bk := bk) f X) = BK.hf (bk := bk) f X ^ l := by
      rw [e1, frobS_X, map_pow]
    refine (congrArg (fun y => ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ y‖) e).trans_le ((norm_toDisc_pow_le l hρ0).trans ?_)
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem scaleRoots_derivative_eval₂_mul {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (P : Polynomial W)
    (s : W) (t : R) :
    c s * Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) =
      c s ^ P.natDegree * Polynomial.eval₂ c t (Polynomial.derivative P) := by
  have h : (P.scaleRoots s).comp (Polynomial.C s * Polynomial.X) = Polynomial.C s ^ P.natDegree * P := by
    have h0 := Polynomial.scaleRoots_eval₂_mul (p := P) (Polynomial.C : W →+* Polynomial W) Polynomial.X s
    rw [Polynomial.eval₂_C_X] at h0
    exact h0
  have h1 := congrArg (fun r => Polynomial.eval₂ c t (Polynomial.derivative r)) h
  simp only [Polynomial.derivative_comp, ← Polynomial.C_pow, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_comp, Polynomial.eval₂_X] at h1
  rw [h1, map_pow]

theorem exists_mul_derivative_scaleRoots_sub_mem {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (I : Ideal R)
    (P a b : Polynomial W) (s z : W) (hab : a * P + b * Polynomial.derivative P = Polynomial.C z) (t x : R)
    (ht : Polynomial.eval₂ c t P ∈ I) (hx : x - c s * t ∈ I) :
    ∃ b' : R, b' * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x - c s ^ P.natDegree * c z ∈ I := by
  refine ⟨Polynomial.eval₂ c t b * c s, ?_⟩
  obtain ⟨w, hw⟩ := Polynomial.sub_dvd_eval_sub x (c s * t) (Polynomial.derivative ((P.scaleRoots s).map c))
  have h1 := scaleRoots_derivative_eval₂_mul c P s t
  have h2 := congrArg (Polynomial.eval₂ c t) hab
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C] at h2
  have h3 : (Polynomial.derivative ((P.scaleRoots s).map c)).eval (c s * t) =
      Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map]
  rw [h3] at hw
  have h4 : Polynomial.eval₂ c t b * c s * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x -
      c s ^ P.natDegree * c z = (Polynomial.eval₂ c t b * c s * w) * (x - c s * t) -
        (c s ^ P.natDegree * Polynomial.eval₂ c t a) * Polynomial.eval₂ c t P := by
    linear_combination (Polynomial.eval₂ c t b * c s) * hw + Polynomial.eval₂ c t b * h1 +
      c s ^ P.natDegree * h2
  rw [h4]
  exact I.sub_mem (I.mul_mem_left _ hx) (I.mul_mem_left _ ht)

theorem eval₂_C_X_powerSeries {W : Type} [CommRing W] (P : Polynomial W) :
    Polynomial.eval₂ (PowerSeries.C : W →+* W⟦X⟧) X P = (P : W⟦X⟧) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, hp, hq, Polynomial.coe_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_C, Polynomial.coe_X]

theorem approxRoot_image_indep_general_rings {W R : Type} [CommRing W] [CommRing R] (l n m c : ℕ) (P a b : Polynomial W)
    (hab : a * P + b * Polynomial.derivative P = Polynomial.C ((l : W) ^ c)) (q : W⟦X⟧)
    (h1 : (P : W⟦X⟧) ∣ q - (l : W⟦X⟧) ^ m * X)
    (h2 : (P : W⟦X⟧) ^ n ∣ Polynomial.eval₂ PowerSeries.C q (P.scaleRoots ((l : W) ^ m)))
    (I : Ideal R) (f g : W⟦X⟧ →+* R) (hC : ∀ w, f (PowerSeries.C w) = g (PowerSeries.C w)) (hX : f X - g X ∈ I)
    (hI : I = Ideal.span {f P}) (hI' : I = Ideal.span {g P}) :
    ∃ k : ℕ, f P ^ n ∣ (l : R) ^ k * (f q - g q) := by
  have hfE : f P ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hgE : g P ∈ I := by rw [hI']; exact Ideal.mem_span_singleton_self _
  have hcomp : f.comp PowerSeries.C = g.comp PowerSeries.C := RingHom.ext hC
  have hroot : ∀ h : W⟦X⟧ →+* R, h P ∈ I →
      ((P.scaleRoots ((l : W) ^ m)).map (h.comp PowerSeries.C)).eval (h q) ∈ I ^ n := by
    intro h hE
    obtain ⟨y, hy⟩ := h2
    rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hy, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hE n)
  have hcong : ∀ h : W⟦X⟧ →+* R, h P ∈ I → h q - (l : R) ^ m * h X ∈ I := by
    intro h hE
    obtain ⟨y, hy⟩ := h1
    have := congrArg h hy
    rw [map_sub, map_mul, map_mul, map_pow, map_natCast] at this
    rw [this]
    exact Ideal.mul_mem_right _ _ hE
  have hxy : f q - g q ∈ I := by
    have : f q - g q = (f q - (l : R) ^ m * f X) - (g q - (l : R) ^ m * g X) + (l : R) ^ m * (f X - g X) := by ring
    rw [this]
    exact I.add_mem (I.sub_mem (hcong f hfE) (hcong g hgE)) (I.mul_mem_left _ hX)
  obtain ⟨b', hb'⟩ := exists_mul_derivative_scaleRoots_sub_mem (f.comp PowerSeries.C) I P a b
    ((l : W) ^ m) _ hab (f X) (f q)
    (by rw [← Polynomial.hom_eval₂, eval₂_C_X_powerSeries]; exact hfE)
    (by rw [map_pow, map_natCast]; exact hcong f hfE)
  have hg := hroot g hgE
  rw [← hcomp] at hg
  have key := GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow R I _ _ _ _ _ n (hroot f hfE) hg hxy hb'
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow, map_pow, map_natCast, ← pow_mul, ← pow_add,
    ← pow_mul] at key
  exact ⟨_, key⟩

theorem approx_root_indep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f q - BK.hf g q)) := by
  intro l _ K bk n m q h1 h2 B f g
  obtain ⟨hC, hX, hI⟩ := GlobalTheory.BSP.IdealSubMembership.main l K bk B f g
  obtain ⟨-, -, hI'⟩ := GlobalTheory.BSP.IdealSubMembership.main l K bk B g f
  obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
  exact approxRoot_image_indep_general_rings l n m c bk.Ep a b hab q h1 h2 B.I (BK.hf f) (BK.hf g) hC hX hI hI'

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.closedDisc_coefficients_topologicallyFree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) ∧ (∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0)) ∧ (∀ y, HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ i, ‖cD i y‖ ≤ r) → ‖y‖ ≤ r) ∧ (∀ z : ι → bk.DS ρ, Filter.Tendsto z Filter.cofinite (nhds 0) → ∃ y, ∀ i, cD i y = z i) ∧ ∀ x, ‖j x‖ = ‖x‖ := by
  first | exact @GlobalTheory.BSP.disc_coefficients | exact GlobalTheory.BSP.disc_coefficients | (intros; apply GlobalTheory.BSP.disc_coefficients <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.nonempty_breuilKisinDatum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), Nonempty (BK K) := by
  first | exact @GlobalTheory.BSP.nonempty_bk_of_finExt | exact GlobalTheory.BSP.nonempty_bk_of_finExt | (intros; apply GlobalTheory.BSP.nonempty_bk_of_finExt <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (g : Hom bk.prism B), B.I = Ideal.span {BK.hf g bk.E} ∧ BK.hf g bk.E ∈ nonZeroDivisors B.A := by
  first | exact @GlobalTheory.BSP.hf_E_span_and_regular | exact GlobalTheory.BSP.hf_E_span_and_regular | (intros; apply GlobalTheory.BSP.hf_E_span_and_regular <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ := by
  first | exact @GlobalTheory.BSP.GaussMul.norm_mul | exact GlobalTheory.BSP.GaussMul.norm_mul | (intros; apply GlobalTheory.BSP.GaussMul.norm_mul <;> assumption)
end
