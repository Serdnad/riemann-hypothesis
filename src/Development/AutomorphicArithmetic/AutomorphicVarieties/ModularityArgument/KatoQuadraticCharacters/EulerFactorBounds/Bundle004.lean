module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle611
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem root_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ^ (l - 1) = 1) : x ∈ c.O := by
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  haveI : NeZero (l - 1) := ⟨hpos.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hg1 : g ∈ rootsOfUnity (l - 1) (ZMod l) := by
    rw [mem_rootsOfUnity, ← hg, pow_orderOf_eq_one]
  rw [← KStar.TotallyRealRoots.map_red_rootsOfUnity (l := l) dvd_rfl] at hg1
  obtain ⟨ζ, hζ, hζg⟩ := hg1
  have hζ1 : ζ ^ (l - 1) = 1 := hζ
  have hp : IsPrimitiveRoot ζ (l - 1) := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rw [← hg, orderOf_dvd_iff_pow_eq_one, ← hζg, ← map_pow, hk, map_one]
  have hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hq := (IsPrimitiveRoot.coe_units_iff.2 hp).map_of_injective hinj
  obtain ⟨i, -, rfl⟩ := hq.eq_pow_of_pow_eq_one hx
  exact pow_mem (c.O.algebraMap_mem _) i

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem mv_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l}
    (hM : ∀ i k, M i k ∈ c.O) (hv : ∀ k, v k ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hM i k) (hv k)

private def rd (l : ℕ) : (ZMod (l ^ 1))ˣ →* (ZMod l)ˣ :=
  Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).toMonoidHom

private theorem rd_val (l : ℕ) [Fact l.Prime] (y : (ZMod (l ^ 1))ˣ) :
    ((rd l y : (ZMod l)ˣ) : ZMod l) = (((y : ZMod (l ^ 1)).val : ℕ) : ZMod l) := by
  rw [ZMod.natCast_val]; rfl

theorem UpperTheory.V.Z.Kato.Nb.sInteg :
    UpperTheory.V.Z.Kato.Nb.SInteg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW
  obtain ⟨-, -, -, -, -, -, hpr, -, -, -, -, χ, -, -, hχ⟩ := hA
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  have hχ' : ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ (rd l (cycMod ℚ Ω l 1 s) : (ZMod l)ˣ) := fun s => by
    rw [rd_val]; exact hχ s
  have hsurj : ∀ u : (ZMod l)ˣ, ∃ s : G ℚ Ω, rd l (cycMod ℚ Ω l 1 s) = u := by
    intro u
    refine ⟨repM l u, ?_⟩
    have h1 := (sCycZ Ω l 1 (repM l u)).1
    have h2 := (hS (l ^ 1) (repM l u)).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [h1]
    exact h2.trans ((hS l 1).2.2.1 u)
  have h1 : ψ 1 = 1 := by
    have := hχ' 1
    rw [map_one, map_one, map_one, Units.val_one, Units.val_one] at this
    exact this.symm
  have hmul : ∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v := by
    intro u v
    obtain ⟨s, rfl⟩ := hsurj u
    obtain ⟨t, rfl⟩ := hsurj v
    rw [← map_mul, ← map_mul, ← hχ', ← hχ', ← hχ', map_mul, Units.val_mul]
  have hpow : ∀ s : G ℚ Ω, χ s ^ (l - 1) = 1 := by
    intro s
    apply Units.ext
    rw [← map_pow, hχ', map_pow, map_pow, ZMod.units_pow_card_sub_one_eq_one, Units.val_one, h1, Units.val_one]
  have hχO : ∀ s : G ℚ Ω, (χ s : Qbar l) ∈ cf.O := fun s =>
    root_mem cf (by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one])
  have hεO : ∀ s : G ℚ Ω, eps l s ∈ cf.O := fun s => cf.O.algebraMap_mem ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])
  let θ : G ℚ Ω →* (Qbar l)ˣ := (cycBar ℚ Ω l ^ e)⁻¹ * χ
  have hθ : ∀ s, thK l e ψ s = (θ s : Qbar l) := fun s => by
    simp only [thK, θ, ← hχ s, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hθO : ∀ s, (θ s : Qbar l) ∈ cf.O := fun s => by
    have h2 : (θ s : Qbar l) = eps l s⁻¹ ^ e * (χ s : Qbar l) := by
      simp only [θ, eps, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow]
    rw [h2]
    exact mul_mem (pow_mem (hεO _) e) (hχO s)
  have hθi : ∀ s, (θ s : Qbar l)⁻¹ = (θ s⁻¹ : (Qbar l)ˣ) := fun s => by
    rw [map_inv, Units.val_inv_eq_inv_val]
  have hρO : ∀ s i k, rhoK W e ψ s i k ∈ cf.O := fun s i k => by
    rw [rhoK, hθ, hθi, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (hθO _) (hW s i k)
  refine ⟨fun s => ?_, h1, hmul, fun u => ?_, hρO, fun s t => ?_, fun c₀ Y hY r s y i => ?_⟩
  · have h2 := nle cf (hθO s⁻¹)
    rw [← hθi, norm_inv, inv_le_one₀ (norm_pos_iff.2 (θ s).ne_zero)] at h2
    rw [hθ]
    exact le_antisymm (nle cf (hθO s)) h2
  · obtain ⟨s, rfl⟩ := hsurj u
    rw [← hχ']
    exact hχO s
  · simp only [rhoK, hθ, mat, map_mul, Units.val_mul, mul_inv, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm ((θ s : Qbar l)⁻¹)]
  · obtain ⟨bB, hbB, b, hb, hc⟩ := hY r 0
    have hF : YfB X l pr W e ψ 0 r N bB s y i ∈ cf.O := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.sum_apply]
      refine sum_mem fun z _ => mv_mem cf (hρO _) (fun k => hpr _ (hbB _ ?_).1 k) i
      have hM := hS (topM l 0 r (N * N))
      have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l 0 r (N * N)) (s * t) = _ := fun s t => (hM s).2.1 t
      have hr := (hM 1).2.2.1
      refine (hM _).2.2.2.1.2 ?_
      have h3 := hm (repM (topM l 0 r (N * N)) z) ((repM (topM l 0 r (N * N)) z)⁻¹ * s *
        repM (topM l 0 r (N * N)) (z * (cycM (topM l 0 r (N * N)) s)⁻¹))
      rw [← mul_assoc, mul_inv_cancel_left, hm, hr, hr, mul_left_comm, mul_inv_cancel, mul_one] at h3
      exact (mul_eq_left.1 h3.symm)
    have h4 := hc s y i
    have h5 := nle cf (add_mem hF (sub_mem (mv_mem cf (hρO s) (hb (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) i) (hb y i)))
    rw [Cg, pow_zero, norm_one] at h4
    have h7 : ∀ a a' : Qbar l, ‖a - a'‖ ≤ 1 → ‖a'‖ ≤ 1 → ‖a‖ ≤ 1 := fun a a' ha ha' => by
      have h6 := (IsUltrametricDist.norm_add_le_max (a - a') a').trans (max_le ha ha')
      rwa [sub_add_cancel] at h6
    exact h7 _ _ h4 h5
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem fin_places (S : Finset ℕ) : {v : HeightOneSpectrum (𝓞 ℚ) | normV v ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 ℚ) | Ideal.absNorm I ≤ S.sup id}.Finite := Ideal.finite_setOf_absNorm_le _
  refine (h.preimage (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun v hv => ?_
  have : normV v ≤ S.sup id := Finset.le_sup (f := id) hv
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this

private theorem scal_iff {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    (∃ t : K, A = t • 1) ↔ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨A 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

private theorem det_of_quad {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (a c : K)
    (hA : ¬ ∃ t : K, A = t • 1) (h : A ^ 2 - a • A + c • (1 : Matrix (Fin 2) (Fin 2) K) = 0) : A.det = c := by
  rw [scal_iff] at hA
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have ht : A 0 0 + A 1 1 - a = 0 := by
    by_contra hne
    apply hA
    refine ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.1 (by linear_combination h01 : A 0 1 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact (mul_eq_zero.1 (by linear_combination h10 : A 1 0 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact sub_eq_zero.1 ((mul_eq_zero.1
        (by linear_combination h00 - h11 : (A 0 0 - A 1 1) * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne)
  rw [Matrix.det_fin_two]
  linear_combination A 0 0 * ht - h00

theorem UpperTheory.V.Z.Kato.Nb.sDetChar :
    UpperTheory.V.Z.Kato.Nb.SDetChar := by
  intro l _ Ω _ _ _ ρ χ hρ hχ ⟨s₀, hs₀⟩ S hF
  have hc : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hρ
  have hχ' : Continuous fun s => (χ s : Qbar l) := Units.continuous_val.comp hχ
  have he : ∀ i j, Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i j := fun i j => hc.matrix_elem i j
  have hU : IsOpen {s | ¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1} := by
    simp only [scal_iff]
    exact (((isClosed_eq (he 0 1) continuous_const).inter
      ((isClosed_eq (he 1 0) continuous_const).inter (isClosed_eq (he 0 0) (he 1 1))))).isOpen_compl
  have hC : IsClosed {s | (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s} := isClosed_eq hc.matrix_det hχ'
  have hD := GlobalTheory.frob_dense_off_finite ℚ Ω _ (fin_places S)
  have key : ∀ s, (¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s := by
    intro s hs
    refine hC.closure_subset_iff.2 ?_ (hD.open_subset_closure_inter hU hs)
    rintro σ ⟨hσ, v, hv, B, hB, hf⟩
    obtain ⟨a, ha⟩ := hF v B σ hv hB hf
    exact det_of_quad _ a _ hσ ha
  intro s
  by_cases hs : ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1
  · obtain ⟨t, ht⟩ := hs
    have h0 := key s₀ (fun ⟨u, hu⟩ => hs₀ u hu)
    have h1 := key (s * s₀) (by
      rintro ⟨u, hu⟩
      rw [map_mul, Units.val_mul, ht, smul_mul_assoc, one_mul] at hu
      have t0 : t ≠ 0 := by
        rintro rfl
        exact (ρ s).ne_zero (by simpa using ht)
      exact hs₀ (t⁻¹ * u) (by rw [mul_smul, ← hu, smul_smul, inv_mul_cancel₀ t0, one_smul]))
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, h0] at h1
    exact mul_right_cancel₀ (χ s₀).ne_zero h1
  · exact key s hs
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsT : UpperTheory.V.Z.Kato.Nb.SEsT := by
  intro Ω _ _ _ ε X l _ N w q M hN hq hqlN hqM hM γ hγ b hb
  have hb' : ∀ g ∈ Gam N l, X.act l ↑g b = b := by
    unfold Tower.BSet at hb
    exact hb.2
  have hN0 : N ≠ 0 := by omega
  have hl0 : l ≠ 0 := (Fact.out : Nat.Prime l).ne_zero
  have hqN : q.Coprime N := (Nat.coprime_mul_iff_right.mp hqlN).2
  have hSD := Betti.isDiam_sgD (l := l) hN0 hl0 hqN
  unfold IsDiam at hSD
  obtain ⟨hSmem, hSq⟩ := hSD
  obtain ⟨hS0N, hS0l⟩ := Subgroup.mem_inf.mp hSmem
  rw [CongruenceSubgroup.Gamma0_mem] at hS0N hS0l
  unfold en at hSq
  unfold DiagMod at hγ
  obtain ⟨-, hγc, hγd⟩ := hγ
  unfold en at hγc hγd
  have hNM : N ∣ M := (dvd_mul_left N l).trans hM
  have hlM : l ∣ M := (dvd_mul_right l N).trans hM
  have hcN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγc
  have hcl : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = 0 := by
    simpa using congrArg (ZMod.castHom hlM (ZMod l)) hγc
  have hdN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = q := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγd
  have hδ : sgD N l q * γ⁻¹ ∈ Gam N l := by
    have hS := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe (sgD N l q))
    have hG := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe γ)
    rw [Matrix.det_fin_two] at hS hG
    push_cast at hS hG
    unfold Gam
    rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
    push_cast
    generalize (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) = S at *
    generalize (γ : Matrix (Fin 2) (Fin 2) ℤ) = G at *
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · linear_combination (↑(S 0 0) : ZMod N) * hdN - (↑(S 0 0) : ZMod N) * hSq + hS
        + (↑(S 0 1) : ZMod N) * hS0N - (↑(S 0 1) : ZMod N) * hcN
    · linear_combination (↑(G 0 0) : ZMod N) * hSq - (↑(G 0 0) : ZMod N) * hdN + hG
        + (↑(G 0 1) : ZMod N) * hcN - (↑(G 0 1) : ZMod N) * hS0N
    · linear_combination (↑(G 1 1) : ZMod N) * hS0N - (↑(S 1 1) : ZMod N) * hcN
    · linear_combination (↑(G 1 1) : ZMod l) * hS0l - (↑(S 1 1) : ZMod l) * hcl
  have hAct : X.act l ↑γ b = X.act l ↑(sgD N l q) b := by
    conv_lhs => rw [← hb' _ hδ]
    rw [Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]
  have hdq : (0 : ℤ) < Matrix.det !![(q : ℤ), 0; 0, 1] := by
    simpa [Matrix.det_fin_two] using hq.pos
  refine ⟨?_, fun s => ?_⟩
  · unfold Tower.heckeT
    simp only [LinearMap.add_apply, LinearMap.sum_apply]
    congr 1
    · symm
      have hinj : ∀ a ∈ Finset.range q, ∀ a' ∈ Finset.range q, a * M % q = a' * M % q → a = a' := by
        intro a ha a' ha' h
        rw [Finset.mem_range] at ha ha'
        have h' : a ≡ a' [MOD q] := Nat.ModEq.cancel_right_of_coprime hqM h
        unfold Nat.ModEq at h'
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h'
      refine Finset.sum_nbij (fun j => j * M % q) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos))
        (fun a ha a' ha' h => hinj a (Finset.mem_coe.mp ha) a' (Finset.mem_coe.mp ha') h) ?_ ?_
      · intro k hk
        obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a _ => a * M % q)
          (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)) (fun a a' ha ha' h => hinj a ha a' ha' h)
          le_rfl k (Finset.mem_coe.mp hk)
        exact ⟨a, Finset.mem_coe.mpr ha, h.symm⟩
      · intro a _
        have hdm := Nat.mod_add_div (a * M) q
        generalize a * M % q = r at hdm ⊢
        generalize a * M / q = t at hdm
        let T : SL(2, ℤ) := ⟨!![1, (t : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
        have hT : T ∈ Gam N l := by
          unfold Gam
          rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
          simp [T]
        have hz : (a : ℤ) * M = r + q * t := by exact_mod_cast hdm.symm
        have hm : !![1, (a : ℤ) * M; 0, (q : ℤ)] = (T : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (r : ℤ); 0, (q : ℤ)] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hz
        rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
          (by simpa [Matrix.det_fin_two] using hq.pos), hb' T hT]
    · rw [← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq,
        ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq, hAct]
  · unfold Tower.diam
    rw [GlobalTheory.T.galois_commutes_hecke_action ε X N l w hN b hb _ hSmem s, hAct]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsFrob : UpperTheory.V.Z.Kato.Nb.SEsFrob := by
  intro Ω _ _ _ l _ v B σ hq hql hB hF
  obtain ⟨hσ, hfr⟩ := hF
  have hmem : ∀ g : Gal(Ω/ℚ), g ∈ ValuationSubring.decompositionSubgroup ℚ B → ∀ y ∈ B, g y ∈ B :=
    fun g hg y hy => (B.subMulAction ℚ).smul_mem' ⟨g, hg⟩ hy
  refine ⟨⟨?_, fun y hy => ⟨hmem σ hσ y hy, hmem σ⁻¹ (inv_mem hσ) y hy,
    hfr y ((B.valuation_le_one_iff y).mpr hy)⟩⟩, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    have h := (hB ((normV v : ℕ) : 𝓞 ℚ)).mpr ((UpperTheory.V.Z.Kato.Nb.mem_place_iff v _).mpr dvd_rfl)
    simpa using h
  · have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [UpperTheory.V.Z.Kato.Nb.mem_place_iff]
      intro hd
      exact hql ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd)
    exact cycZ_of_isFrob hl hB ⟨hσ, hfr⟩
end
