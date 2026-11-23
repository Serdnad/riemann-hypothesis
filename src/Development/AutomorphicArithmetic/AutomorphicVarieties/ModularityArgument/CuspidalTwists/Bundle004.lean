module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Cu

private theorem closed_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F E : IntermediateField ℚ Ω) :
    IsClosed ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) := by
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) =
      ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rfl
  rw [e]
  exact isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)

private theorem lim_pt {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (S : Set Γ) (hS : IsClosed S) (g : Γ)
    (hg : (l : ℤ_[l]) ∣ (ε g : ℤ_[l]) - 1) (hm : ∀ n : ℕ, g ^ l ^ n ∈ S) : ∃ h ∈ S, ε h = 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have h2 := dvd_sub_pow_of_dvd_sub hg n
    rw [one_pow] at h2
    have h3 := (pow_dvd_pow _ n.le_succ).trans h2
    rw [map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h3
  obtain ⟨h, hh, hc⟩ := hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))
  refine ⟨h, hh, Units.ext ?_⟩
  have hc' := hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt
  exact eq_of_nhds_neBot (hc'.clusterPt.mono ht)

private theorem dvd_of_om {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.om g = 1) : (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - 1 := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  have h := hD.om_bar g
  simp only [Raw.bar, hg, Units.val_one] at h
  have h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0 := by
    rw [map_sub, map_sub, map_one, h, sub_eq_zero]
    rfl
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := fun hu => h1 (hu.map _)
  rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  (T : Tower D)

private theorem rb_al (g : G T.F Ω) :
    T.rb wAl g = residue c.O ((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ : c.Oˣ) : c.O) := by
  show residue c.O (((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
    (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = _
  rw [zpow_one, zpow_zero, mul_one]

private theorem rb_le {T₀ : Tower D} (h : T₀.Le T) (g : G T.F Ω) : T.rb wAl g = T₀.rb wAl (resLe h.le g) := by
  rw [rb_al, rb_al, h.pr]
  try rfl

private noncomputable def eta : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt wAl)

private theorem eta_val (g : G T.F Ω) : (eta T g : ResidueField c.O) = T.rb wAl g := rfl

private theorem eta_iff {K' : IntermediateField ℚ Ω}
    (hon : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup → T.rb wAl g = 1)
    (hoff : ∀ g : G T.F Ω, resQ T.F g ∉ K'.fixingSubgroup → T.rb wAl g = -1) (hn : (-1 : ResidueField c.O) ≠ 1)
    (g : G T.F Ω) : eta T g = 1 ↔ resQ T.F g ∈ K'.fixingSubgroup := by
  rw [← Units.val_eq_one, eta_val]
  by_cases h : resQ T.F g ∈ K'.fixingSubgroup
  · exact ⟨fun _ => h, fun _ => hon g h⟩
  · rw [hoff g h]
    exact ⟨fun e => absurd e hn, fun e => absurd e h⟩

private theorem eta_sq {K' : IntermediateField ℚ Ω}
    (hon : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup → T.rb wAl g = 1)
    (hoff : ∀ g : G T.F Ω, resQ T.F g ∉ K'.fixingSubgroup → T.rb wAl g = -1) (g : G T.F Ω) : eta T g ^ 2 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, eta_val, Units.val_one]
  by_cases h : resQ T.F g ∈ K'.fixingSubgroup
  · rw [hon g h, one_pow]
  · rw [hoff g h, neg_one_sq]

private theorem eta_om (hD : D.Good) (K' : IntermediateField ℚ Ω)
    (hk' : ∀ g, eta T g = 1 ↔ resQ T.F g ∈ K'.fixingSubgroup) (hsq : ∀ g, eta T g ^ 2 = 1)
    (hne : ∀ g ∈ T.G', resQ T.F g ∈ K'.fixingSubgroup) (g : G T.F Ω) (hg' : g ∈ T.GalL)
    (hg : D.om (resQ T.F g) = 1) : eta T g = 1 := by
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  have hk'' : ∀ g, eta T g = 1 ↔ g ∈ K'.fixingSubgroup.comap (resQ T.F) := fun g => by
    rw [Subgroup.mem_comap, hk']
  have hc : Continuous fun h : G T.F Ω => g⁻¹ * h := continuous_const_mul _
  have h0 : IsClosed (T.GalL : Set (G T.F Ω)) := closed_fix T.F T.K
  have hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1 := dvd_of_om D hD (resQ T.F g) hg
  obtain ⟨h, ⟨h1, h2⟩, h3⟩ := lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _
    (h0.inter ((closed_fix T.F K').preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by
      refine (hk'' _).1 ?_
      obtain ⟨m, hm⟩ := (hl.out.odd_of_ne_two hD.l_odd).pow (n := n)
      rw [map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, hsq g, one_pow, one_mul, inv_mul_cancel]⟩)
  have h4 : eta T h = 1 := (hk' h).2 (hne h ⟨h1, h3⟩)
  have h5 := (hk'' _).2 h2
  rwa [map_mul, h4, mul_one, map_inv, inv_eq_one] at h5

private theorem eta_mul (g : G T.F Ω) :
    eta T g * Raw.bar (chi D T.pr 1) (resQ T.F g) = Raw.bar (chi D T.pr 0) (resQ T.F g) ∧
    eta T g * Raw.bar (chi D T.pr 3) (resQ T.F g) = Raw.bar (chi D T.pr 2) (resQ T.F g) := by
  have e : (T.fr ∅).rt wAl g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ := by
    show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
      (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) = _
    rw [zpow_zero, zpow_one, mul_one]
  have e' : (T.fr ∅).rt wAl g = chi D T.pr 2 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹ := by
    rw [e]
    generalize resQ T.F g = s
    cases T.pr
    · show D.al s * D.Psi s * (D.Psi s)⁻¹ = D.al s * 1⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_right]
    · show D.al s * 1⁻¹ = D.al s * D.Psi s * (D.Psi s)⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_right]
  rw [eta_val]
  constructor
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]

private theorem eta_mul' (hsq : ∀ g, eta T g ^ 2 = 1) (g : G T.F Ω) {u v : ResidueField c.O} (h : eta T g * u = v) :
    eta T g * v = u := by
  rw [← h, ← mul_assoc, ← Units.val_mul, ← pow_two, hsq g, Units.val_one, one_mul]

private noncomputable def etaL : T.GalL →* (ResidueField c.O)ˣ := (eta T).comp T.GalL.subtype

private theorem etaL_app (g : T.GalL) : etaL T g = eta T g := rfl

private theorem etaL_sq (hsq : ∀ g, eta T g ^ 2 = 1) : etaL T ^ 2 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, hsq]

private theorem etaL_perm (hsq : ∀ g, eta T g ^ 2 = 1) (i : Fin 4) : ∃ j, ∀ g : T.GalL,
    etaL T g * Raw.bar (chi D T.pr i) (resQ T.F g) = Raw.bar (chi D T.pr j) (resQ T.F g) := by
  simp only [etaL_app]
  match i with
  | 0 => exact ⟨1, fun g => eta_mul' T hsq g (eta_mul T g).1⟩
  | 1 => exact ⟨0, fun g => (eta_mul T g).1⟩
  | 2 => exact ⟨3, fun g => eta_mul' T hsq g (eta_mul T g).2⟩
  | 3 => exact ⟨2, fun g => (eta_mul T g).2⟩

end

theorem UpperTheory.V.Cu.alNe : AlNe := by
  intro Ω _ _ _ l hl d T hT hO
  by_contra hne
  have hne' : ∀ g ∈ T.G', resQ T.F g ∈ d.K'.fixingSubgroup := fun g hg => by_contra fun h => hne ⟨g, hg, h⟩
  have hon : ∀ g : G T.F Ω, resQ T.F g ∈ d.K'.fixingSubgroup → T.rb wAl g = 1 := fun g hg => by
    rw [rb_le T hT]
    exact d.quad.on (resLe hT.le g) hg
  have hoff : ∀ g : G T.F Ω, resQ T.F g ∉ d.K'.fixingSubgroup → T.rb wAl g = -1 := fun g hg => by
    rw [rb_le T hT]
    exact d.quad.off (resLe hT.le g) hg
  have hn : (-1 : ResidueField d.c.O) ≠ 1 := by
    obtain ⟨g, -, hg⟩ := hO.g3 wAl (by decide)
    by_cases h : resQ T.F g ∈ d.K'.fixingSubgroup
    · exact absurd (hon g h) hg
    · rw [hoff g h] at hg
      exact hg
  have hsq := eta_sq T hon hoff
  have key := hO.g3' (etaL T) (etaL_sq T hsq)
    (fun g hg => by rw [etaL_app]; exact eta_om T d.ctx.1 d.K' (eta_iff T hon hoff hn) hsq hne' g g.2 hg)
    (etaL_perm T hsq)
  obtain ⟨g, hg, hg'⟩ := hO.g3 wAl (by decide)
  have h1 := etaL_app T ⟨g, hg⟩
  rw [key, MonoidHom.one_apply] at h1
  apply hg'
  rw [← eta_val, ← h1, Units.val_one]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu.RankFourResidualFlag

section Alg

variable {R : Type} [CommRing R]

def mat (P b e : R) : M4 R := !![P, 0, 0, 0; 0, P * e, 0, 0; 0, -(b * e), e, 0; b, 0, 0, 1]

theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

theorem flg_map {R' : Type} [CommRing R'] (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  rw [flg_eq, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem flg_10 (x s : R) : flg x s 1 0 = s := by
  rw [flg_eq]
  simp

theorem conj_diag (x s dl P b e : R) (i : Fin 4) :
    (adj (flg x s) * (dl • mat P b e) * flg x s) i i = (dl • mat P b e) i i := by
  rw [flg_eq]
  fin_cases i <;> simp [adj_apply, mat, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev]

theorem mat_supp {S : Finset (ℤ × ℤ)} (h1 : wt 2 1 ∈ S) (h2 : wt 3 0 ∈ S) (dl P b e : R) : SuppM S (dl • mat P b e) := by
  intro i j hij hw
  fin_cases i <;> fin_cases j <;> first | (simp [mat]; done) | exact absurd h1 hw | exact absurd h2 hw | exact absurd rfl hij

theorem tn_map {R' : Type} [CommRing R'] (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

theorem tn_eq (g t : M2 R) (hg : g 0 1 = 0) (ht1 : t 0 1 = 0) (ht2 : t 1 0 = 0) (ht0 : t 0 0 = 1)
    (hg1 : g 1 1 = 1) : tn g t = mat (g 0 0) (g 1 0) (t 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, mat, hg, ht1, ht2, ht0, hg1]

theorem res_mul {O : Type} [CommRing O] [IsLocalRing O] (u v : Oˣ) {t : ResidueField O}
    (h : residue O ((u * v⁻¹ : Oˣ) : O) = t) : residue O (u : O) = t * residue O (v : O) := by
  have e : (u : O) = ((u * v⁻¹ : Oˣ) : O) * (v : O) := by simp
  rw [e, map_mul, h]

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem chi_mul {c : Coef l} (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) :
    chi D pr 0 g * chi D pr 3 g = chi D pr 1 g * chi D pr 2 g := by
  cases pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]

private theorem inc_mem {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  have hint : (inc h).IsIntegral := by
    intro y
    obtain ⟨p, hp, e⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact e
  haveI : IsLocalHom (inc h) := hint.isLocalHom (Subalgebra.inclusion_injective h)
  exact map_nonunit (inc h) x hx

theorem eq_of_res {c c' : Coef l} (h : c.O ≤ c'.O) {R : Type} [CommRing R]
    (f : c'.O →+* R) (hf : ∀ y ∈ maximalIdeal c'.O, f y = 0) {x y : c.O} (e : residue c.O x = residue c.O y) :
    f (inc h x) = f (inc h y) := by
  have h1 : x - y ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_sub, e, sub_self]
  have h2 := hf _ (inc_mem h h1)
  rwa [map_sub, map_sub, sub_eq_zero] at h2

end UpperTheory.V.Cu.RankFourResidualFlag

open UpperTheory.V.Cu.RankFourResidualFlag in
theorem UpperTheory.V.Cu.resOf4 : UpperTheory.V.Cu.ResOf4 := by
  intro Ω _ _ _ l _ d T hT W R _ f hf
  have hpr : T.pr = d.T₀.pr := hT.pr

  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (Phi d.D d.T₀.pr d.k g : d.c.O)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have h01 : ∀ g, f (d.ρ₁ g 0 1) = 0 := fun g => hf _ (d.mod.red g).2.2
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t01 : ∀ g, f (d.τ g 0 1) = 0 := fun g => hf _ (d.tau.red g).2
  have hne : ∀ u : d.c.Oˣ, f (inc d.h (u : d.c.O)) ≠ 0 := fun u => by
    have : IsUnit (f (inc d.h (u : d.c.O))) := (u.isUnit.map (inc d.h)).map f
    exact this.ne_zero

  have sgnK : ∀ g : G T.F Ω, ∃ e : R, (e = 1 ∨ e = -1) ∧ f (d.τ (resQ T.F g) 1 1) = e ∧ f (d.τ (resQ T.F g) 1 0) = 0 ∧
      f (inc d.h (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) * e ∧
      f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 3 (resQ T.F g) : d.c.O)) * e := by
    intro g
    have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
    have hrb : ∀ t : ResidueField d.c.O, d.T₀.rb wAl (resLe hT.le g) = t →
        residue d.c.O (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O) =
          t * residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) := fun t ht => by
      apply res_mul
      simp only [Tower.rb, Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, wAl, zpow_one,
        zpow_zero, mul_one, hres] at ht
      exact ht
    have hprod := congrArg (fun u : d.c.Oˣ => f (inc d.h (u : d.c.O))) (chi_mul d.D d.T₀.pr (resQ T.F g))
    simp only [Units.val_mul, map_mul] at hprod
    have h0 := hne (chi d.D d.T₀.pr 0 (resQ T.F g))
    by_cases hK : resQ T.F g ∈ d.K'.fixingSubgroup
    · have e1 := hrb 1 (d.quad.on _ (by rwa [hres]))
      rw [one_mul] at e1
      have e2 := eq_of_res d.h f hf e1.symm
      obtain ⟨a1, a2⟩ := d.tau.on _ hK
      refine ⟨1, Or.inl rfl, by rw [a1, t00], by rw [a2, t01], by rw [e2, mul_one], ?_⟩
      rw [e2] at hprod
      rw [mul_one]
      exact (mul_left_cancel₀ h0 hprod).symm
    · have e1 := hrb (-1) (d.quad.off _ (by rwa [hres]))
      have e1' : residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) =
          residue d.c.O (-(chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) := by
        rw [map_neg, e1]
        ring
      have e2 := eq_of_res d.h f hf e1'
      rw [map_neg, map_neg] at e2
      obtain ⟨a1, a2⟩ := d.tau.off _ hK
      refine ⟨-1, Or.inr rfl, by rw [a1, map_neg, t00], by rw [a2, map_neg, t01, neg_zero], by rw [e2]; ring, ?_⟩
      rw [e2] at hprod
      have := mul_left_cancel₀ h0 (hprod.trans (by ring) : _ = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) *
        (-f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O))))
      rw [this]
      ring

  have hr : ∀ g, ((d.Q T).map f).r g = f (inc d.h (d.δ (resQ T.F g) : d.c.O)) •
      tn ((d.ρ₁ (resQ T.F g)).map f) ((d.τ (resQ T.F g)).map f) := fun g => by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have key : ∀ g : G T.F Ω, ∃ e P b dl : R, ((d.Q T).map f).r g = dl • mat P b e ∧
      (f.comp (inc d.h)) ((T.fr W).χ 0 g : d.c.O) = dl * P ∧ (f.comp (inc d.h)) ((T.fr W).χ 1 g : d.c.O) = dl * (P * e) ∧
      (f.comp (inc d.h)) ((T.fr W).χ 2 g : d.c.O) = dl * e ∧ (f.comp (inc d.h)) ((T.fr W).χ 3 g : d.c.O) = dl := by
    intro g
    obtain ⟨e, -, he, he10, e1, e2⟩ := sgnK g
    have hrg := hr g
    have hχ : ∀ i, (f.comp (inc d.h)) ((T.fr W).χ i g : d.c.O) =
        f (inc d.h (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O)) := fun i => by
      rw [← hpr]
      rfl
    generalize resQ T.F g = g' at he he10 e1 e2 hrg hχ
    have r0 : f (inc d.h (chi d.D d.T₀.pr 0 g' : d.c.O)) =
        f (inc d.h (d.δ g' : d.c.O)) * f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)) := by
      rw [← map_mul, ← map_mul]
      apply eq_of_res d.h f hf
      rw [map_mul]
      exact d.tw.red0 g'
    have r3 := eq_of_res d.h f hf (d.tw.red3 g')
    refine ⟨e, f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)), f (d.ρ₁ g' 1 0), f (inc d.h (d.δ g' : d.c.O)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrg, tn_eq _ _ (by rw [Matrix.map_apply]; exact h01 _) (by rw [Matrix.map_apply]; exact t01 _)
        (by rw [Matrix.map_apply]; exact he10) (by rw [Matrix.map_apply]; exact t00 _) (by rw [Matrix.map_apply]; exact h11 _)]
      simp only [Matrix.map_apply]
      rw [h00, he]
    · rw [hχ 0]
      exact r0
    · rw [hχ 1, e1, r0]
      ring
    · rw [hχ 2, e2, r3]
    · rw [hχ 3]
      exact r3
  have hn : ∀ v, ((d.Q T).map f).n v = flg (f (d.x (T.pl v))) (f (d.s (T.pl v))) := fun v => flg_map f _ _
  have hs : ∀ S : Finset (ℤ × ℤ), wt 2 1 ∈ S → wt 3 0 ∈ S → Supp S ((d.Q T).map f).r := fun S h1 h2 g => by
    obtain ⟨e, P, b, dl, h, -⟩ := key g
    rw [h]
    exact mat_supp h1 h2 dl P b e
  have hsM : Supp nM ((d.Q T).map f).r := hs nM (by decide) (by decide)
  refine ⟨⟨fun g i => ?_, fun (v : T.ι) s _ i => ?_, Or.inr hsM⟩, hsM, ⟨hs aA (by decide) (by decide), fun v => ?_⟩, fun g => ?_⟩
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key g
    rw [h]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key s
    show (adj (((d.Q T).map f).n v) * ((d.Q T).map f).r s * ((d.Q T).map f).n v) i i = _
    rw [hn v, h, conj_diag]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · rw [hn, flg_10]
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> simp
  · rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, h00, h11, h01]
    ring
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section
variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_map {S : Type} [CommRing S] {J : Ideal S} (φ : R →+* S) (h : I ≤ J.comap φ) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun g => φ (f g) := fun N =>
  (hf N).comp (Ideal.quotientMap (J ^ N) φ ((Ideal.pow_right_mono h N).trans (Ideal.le_comap_pow φ N)))

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x :=
  fun N => (hf N).mul (hg N)

private theorem ac_neg {f : Γ → R} (hf : AdicCont I f) : AdicCont I fun x => -f x :=
  fun N => (hf N).neg

private theorem ac_tn {f t : Γ → M2 R} (hf : ∀ i j, AdicCont I fun g => f g i j)
    (ht : ∀ i j, AdicCont I fun g => t g i j) (i j : Fin 4) : AdicCont I fun g => tn (f g) (t g) i j := by
  fin_cases i <;> fin_cases j <;> simp [tn] <;>
    first
    | exact ac_mul (hf _ _) (ht _ _)
    | exact ac_neg (ac_mul (hf _ _) (ht _ _))

end

theorem contOf4 : ContOf4 := by
  intro Ω _ _ _ l _ d T
  have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
  have hm : maximalIdeal d.c.O ≤ (maximalIdeal d.c₁.O).comap (inc d.h) := fun x hx =>
    (UpperTheory.V.Fr.sc_norm l d.c₁ (inc d.h x)).2.2 ((UpperTheory.V.Fr.sc_norm l d.c x).2.1 hx)
  have h1 : (d.Q T).Cont (maximalIdeal d.c₁.O) := fun i j N =>
    (ac_mul (ac_map (inc d.h) hm d.tw.cont) (ac_tn d.mod.cont d.tau.cont i j) N).comp_continuous hc
  exact ⟨h1, fun R _ f hf i j => ac_map (J := ⊥) f (fun y hy => Ideal.mem_comap.2 (Ideal.mem_bot.2 (hf y hy))) (h1 i j)⟩

end UpperTheory.V.Cu

end
end
