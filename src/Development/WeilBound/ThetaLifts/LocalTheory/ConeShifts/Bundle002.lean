module

public import Development.WeilBound.ThetaLifts.LocalTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle005
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealB
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle001
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

theorem int_fin {α Y : Type} [MeasurableSpace α] (μ : Measure α) (G : α → Y → ℂ) (w : α → ℂ) (hf : (Set.range G).Finite)
    (hm : ∀ g, MeasurableSet {a | G a = g}) (D : Set α) (hD : ∀ a ∉ D, G a = 0) (hw : IntegrableOn w D μ)
    (S : Submodule ℂ (Y → ℂ)) (hS : ∀ a, G a ∈ S) :
    (∀ y, Integrable (fun a => G a y * w a) μ) ∧ (fun y => ∫ a, G a y * w a ∂μ) ∈ S := by
  let s := hf.toFinset.erase 0
  have e : ∀ y a, G a y * w a = ∑ g ∈ s, g y * ({a | G a = g} : Set α).indicator w a := fun y a => by
    by_cases h0 : G a = 0
    · rw [h0, Pi.zero_apply, zero_mul, Finset.sum_eq_zero]
      intro g hg
      rw [Set.indicator_of_notMem, mul_zero]
      exact fun h => (Finset.mem_erase.1 hg).1 (h.symm.trans h0)
    · rw [Finset.sum_eq_single (G a), Set.indicator_of_mem (by rfl)]
      · intro g _ hne
        rw [Set.indicator_of_notMem (s := {a | G a = g}) (fun h => hne (Eq.symm h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨h0, hf.mem_toFinset.2 ⟨a, rfl⟩⟩) h
  have hi : ∀ g ∈ s, Integrable (({a | G a = g} : Set α).indicator w) μ := fun g hg =>
    (integrable_indicator_iff (hm g)).2 (hw.mono_set fun a ha => by
      by_contra hn
      exact (Finset.mem_erase.1 hg).1 (Eq.trans (Eq.symm ha) (hD a hn)))
  refine ⟨fun y => ?_, ?_⟩
  · simp only [e y]
    exact integrable_finsetSum _ fun g hg => (hi g hg).const_mul _
  · have : (fun y => ∫ a, G a y * w a ∂μ) = ∑ g ∈ s, (∫ a, ({a | G a = g} : Set α).indicator w a ∂μ) • g := by
      funext y
      simp only [e y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum _ fun g hg => (hi g hg).const_mul _]
      exact Finset.sum_congr rfl fun g _ => by rw [integral_const_mul, mul_comm]
    rw [this]
    refine S.sum_mem fun g hg => S.smul_mem _ ?_
    obtain ⟨a, rfl⟩ := hf.mem_toFinset.1 (Finset.mem_erase.1 hg).2
    exact hS a

section Schr
variable {k κ : Type} [CommRing k] [Invertible (2 : k)] [TopologicalSpace k] [IsTopologicalRing k] [Fintype κ]
  {ψ : AddChar k ℂ}

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_mul (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : k) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have := invOf_two_add_invOf_two (R := k)
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * this

theorem schr_fix (hψ : IsLocallyConstant ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have h : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), ∀ x ∈ tsupport φ,
      ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) = 1 ∧ φ (x + w.1) = φ x ∧ φ (x - w.1) = φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
    have c1 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 ⬝ᵥ z.1.2 + ⅟(2 : k) * (z.1.1 ⬝ᵥ z.1.2) := by
      unfold dotProduct; fun_prop
    have c2 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 + z.1.1 := by fun_prop
    have c3 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 - z.1.1 := by fun_prop
    have e1 := (hψ.comp_continuous c1).eventually_eq (0, x)
    have e2 := (hφ.1.comp_continuous c2).eventually_eq (0, x)
    have e3 := (hφ.1.comp_continuous c3).eventually_eq (0, x)
    have e4 := (hφ.1.comp_continuous (continuous_snd (X := (κ → k) × (κ → k)))).eventually_eq (0, x)
    filter_upwards [e1, e2, e3, e4] with z a b c d
    simp only [Function.comp_apply, Prod.snd_zero, Prod.fst_zero, dotProduct_zero, mul_zero, add_zero, sub_zero,
      AddChar.map_zero_eq_one] at a b c d
    exact ⟨a, b.trans d.symm, c.trans d.symm⟩
  filter_upwards [h] with w hw
  funext x
  by_cases hx : x ∈ tsupport φ
  · rw [schr, (hw x hx).1, (hw x hx).2.1, one_mul]
  · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [schr, h0]
    by_cases h1 : x + w.1 ∈ tsupport φ
    · have := (hw _ h1).2.2
      rw [add_sub_cancel_right, h0] at this
      rw [← this, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]

theorem schr_lc (hψ : IsLocallyConstant ψ) {φ : (κ → k) → ℂ} (hs : ∀ w, schr ψ w φ ∈ SB (κ → k)) :
    IsLocallyConstant fun w => schr ψ w φ := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun w₀ => ?_
  have c : Continuous fun w : (κ → k) × (κ → k) => ⅟(2 : k) * (w.1 ⬝ᵥ w₀.2 - w₀.1 ⬝ᵥ w.2) := by
    unfold dotProduct; fun_prop
  have h : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ (w + w₀) φ = schr ψ w₀ φ := by
    filter_upwards [schr_fix hψ (hs w₀), (hψ.comp_continuous c).eventually_eq 0] with w a b
    simp only [Function.comp_apply, Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero, mul_zero,
      AddChar.map_zero_eq_one] at b
    rw [schr_mul, b, one_smul] at a
    exact a
  have t : Tendsto (fun w : (κ → k) × (κ → k) => w - w₀) (𝓝 w₀) (𝓝 0) := by
    have := (continuous_sub_right w₀).tendsto w₀
    rwa [sub_self] at this
  filter_upwards [t.eventually h] with w hw
  rwa [sub_add_cancel] at hw

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_comm (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  rw [schr_mul, schr_mul, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w]
  congr 2
  have := invOf_two_add_invOf_two (R := k)
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * this

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_lin (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ) (c : ℂ) :
    schr ψ w (φ + c • φ') = schr ψ w φ + c • schr ψ w φ' := by
  funext x; simp only [schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

end Schr

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_uniq {v : Pl F} {T} {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ :=
  GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ φ₂ hφ fun r hr => (h₁ r hr).symm.trans (h₂ r hr)

theorem opF_eq {v : Pl F} {T} {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : φ₁ ∈ SB _) (h : Acts (evFin F v) T φ φ₁) :
    opF v T φ = φ₁ := by
  have ex : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ := ⟨φ₁, h₁, h⟩
  rw [opF, dite_eq_left ex]
  exact acts_uniq hφ ex.choose_spec.2 h

theorem acts_comp {v : Pl F} {S T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (hT : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) S φ₁ φ₂) :
    Acts (evFin F v) (fun Φ => S (T Φ)) φ φ₂ := fun r hr => by
  show S (T _) = _
  rw [h₁ r hr]
  exact h₂ r ⟨hr.1, h₁ r hr ▸ hT _ hr.2⟩

theorem pure_cancel {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, w v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (v : Pl F) {g : SInf F κ}
    (hg : g ≠ 0) {a b : (κ → Fv F v) → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v a) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v b)) : a = b := by
  have := PositivityTheory.ThKF.tensInj F κ w hne hstd {v} 2 ![1, -1] ![g, g] ![Function.update w v a, Function.update w v b]
    (fun i u hu => by
      have : u ≠ v := fun e => hu (Finset.mem_singleton.2 e)
      fin_cases i <;> simp [Function.update_of_ne this]) (by simp [Fin.sum_univ_two, h])
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hg (SchwartzMap.ext hn)
  funext y
  let y' : ∀ u : ({v} : Finset (Pl F)), κ → Fv F u := fun u => (Finset.mem_singleton.1 u.2).symm ▸ y
  let m : MultilinearMap (RingHom.id ℂ) (fun u : ({v} : Finset (Pl F)) => (κ → Fv F u) → ℂ) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ _ ℂ).compLinearMap fun u => LinearMap.proj (y' u)
  let ez : SInf F κ →ₗ[ℂ] ℂ := ⟨⟨fun f => f z, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ ez (PiTensorProduct.lift m))) this
  have hm : ∀ c : (κ → Fv F v) → ℂ, m (fun u => Function.update w v c u) = c y := fun c => by
    simp only [m, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply]
    rw [Fintype.prod_eq_single (⟨v, Finset.mem_singleton_self v⟩ : ({v} : Finset (Pl F)))
      fun u hu => absurd (Subtype.ext (Finset.mem_singleton.1 u.2)) hu]
    simp [y']
  simp only [Fin.sum_univ_two, map_add (f := _), map_smul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, PiTensorProduct.lift.tprod,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, LinearMap.mul_apply', hm] at h2
  have h3 : g z * (a y - b y) = 0 := by
    change (1 : ℂ) • (g z * a y) + (-1 : ℂ) • (g z * b y) = 0 at h2
    simp only [smul_eq_mul] at h2
    linear_combination h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hz)

end PositivityTheory.ThKG.Loc.Cone.Fin

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Id

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes WithZero
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Idele
open Formalism.L2.Host (IsUnitAt IsUnifAt atFin unif unif_spec)
open FractionalIdeal (count)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem lines {B : Base F E} (hB : B.IsGood σ) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {H : Plane E n n₁} {H' : Plane E d d₁} {r s r' s' i j i' j' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (h : H.IsAdapted σ B X X₁ i j) (h' : H'.IsAdapted σ B W W₁ i' j') (hσ : ∀ x, σ (σ x) = x) :
    (Line X.L H.x H.𝔟 ∧ Line X.L H.y (1 * (cj hσ H.𝔟)⁻¹)) ∧
      Line W.L H'.x H'.𝔟 ∧ Line W.L H'.y (codiff E * (cj hσ H'.𝔟)⁻¹) :=
  ⟨plane_lines hσ (ε := 1) (mul_one 1) (fun a b => by rw [hX.herm, one_mul]) hX.lat.toIsLattice (fun y => by
      rw [hX.dual]
      refine forall₂_congr fun x _ => ?_
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨fun e => ⟨⟨_, e⟩, rfl⟩, fun ⟨o, e⟩ => e ▸ RingOfIntegers.isIntegral_coe o⟩) one_ne_zero h,
    plane_lines hσ (ε := -1) (by ring) (fun a b => by rw [hW.skew, neg_one_mul]) hW.lat.toIsLattice (fun y => by
      rw [hW.dual]
      exact forall₂_congr fun x _ => inD_iff _) codiff_ne_zero h'⟩

theorem memA {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {H : Plane E n n₁} {H' : Plane E d d₁} {𝔭 𝔮 : FI E}
    (a : Line X.L H.x 𝔭) (b : Line W.L H'.y 𝔮) (v : Pl F) (l : (AE F E)ˣ) :
    idem F v • shiftA H H' l ∈ latAtV X W v ↔ InAt (𝔭 * 𝔮) v (l : AE F E) := by
  rw [shiftA, ← smul_assoc, line_lat a b, lat_iff (mul_ne_zero a.ne b.ne)]

theorem memB (hσ : ∀ x, σ (σ x) = x) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {H : Plane E n n₁} {H' : Plane E d d₁}
    {𝔭 𝔮 : FI E} (a : Line X.L H.y 𝔭) (b : Line W.L H'.x 𝔮) (v : Pl F) (l : (AE F E)ˣ) :
    idem F v • shiftB σ H H' l ∈ latAtV X W v ↔ InAt (cj hσ (𝔭 * 𝔮)) v (l : AE F E) := by
  rw [shiftB, ← smul_assoc, line_lat a b, lat_iff (mul_ne_zero a.ne b.ne), inAt_cj_iff hσ (mul_ne_zero a.ne b.ne)]

theorem idealId0 : IdealId0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hB hX hW h h' u hu
  have hσ := PositivityTheory.ThK.Vac.sigma_sigma hB.cm
  obtain ⟨⟨a, a'⟩, b, b'⟩ := lines hB hX hW h h' hσ
  rcases hu with rfl | rfl
  · exact ⟨_, mul_ne_zero a.ne b'.ne, memA a b'⟩
  · exact ⟨_, cj_ne hσ (mul_ne_zero a'.ne b.ne), memB hσ a' b⟩

theorem idealId' : IdealId' := by
  refine ⟨1, 1, -1, -1, ?_⟩
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hB hX hW h h' hi hj hi' hj' u e₁ e₂ hu
  have hσ := PositivityTheory.ThK.Vac.sigma_sigma hB.cm
  obtain ⟨⟨a, a'⟩, b, b'⟩ := lines hB hX hW h h' hσ
  have pD := pr_codiff hB
  have p1 : Pr B.P (1 : FI E) := fun w _ => FractionalIdeal.count_one _ _
  have pa := plane_pr hσ hB.cm one_ne_zero p1 hX.bas h hi hj ⟨a, a'⟩
  have pb := plane_pr hσ hB.cm codiff_ne_zero pD hW.bas h' hi' hj' ⟨b, b'⟩
  have ca := cj_ne hσ a.ne
  have cb := cj_ne hσ b.ne
  have tr : ∀ ν : Chr F E, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range ν 0 →
      ∀ x : (AF F)ˣ, ν (ideleMap F E x) = 1 := fun ν hν x => hν.triv_of_even Even.zero x
  rcases hu with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨_, mul_ne_zero a.ne b'.ne, memA a b',
      pa.mul a.ne b'.ne (pD.mul codiff_ne_zero (inv_ne_zero cb) (pb.cj hσ hB.cm b.ne).inv), fun ν _ hν hu => ?_⟩
    rw [idealVal_mul _ a.ne b'.ne, idealVal_mul _ codiff_ne_zero (inv_ne_zero cb), idealVal_inv,
      idealVal_cj hσ b.ne pb hu (nu_conj hB.cm (tr ν hν)), idealVal_codiff hB (tr ν hν) hu]
    simp
  · have pp : Pr B.P (1 * (cj hσ H.𝔟)⁻¹ * H'.𝔟) :=
      (p1.mul (one_ne_zero (α := FI E)) (inv_ne_zero ca) (pa.cj hσ hB.cm a.ne).inv).mul a'.ne b.ne pb
    refine ⟨_, cj_ne hσ (mul_ne_zero a'.ne b.ne), memB hσ a' b, pp.cj hσ hB.cm (mul_ne_zero a'.ne b.ne), fun ν _ hν hu => ?_⟩
    rw [idealVal_cj hσ (mul_ne_zero a'.ne b.ne) pp hu (nu_conj hB.cm (tr ν hν)), idealVal_mul _ a'.ne b.ne, one_mul, idealVal_inv,
      idealVal_cj hσ a.ne pa hu (nu_conj hB.cm (tr ν hν))]
    simp [mul_comm]

end PositivityTheory.ThKG.Loc.Cone.Id

end
end
