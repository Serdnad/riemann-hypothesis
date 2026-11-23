module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle012
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TwoSidedIdeal.Instances
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.sel_desc_fac {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G0 : Glob l L} (g : G.Hom G') (h : G.Hom G0)
    {n : ℕ} {R : Type} [CommRing R] (t : R) (ht : IsNilpotent t) (hl : (l : R) = 0)
    (H : Subgroup G0.Γ) [H.Normal] (ho : IsOpen (H : Set G0.Γ)) (hle : H ≤ G0.η.ker)
    (hk : g.p.ker = PL l (H.comap h.p))
    (ρ : G0.G₀ → Matrix (Fin n) (Fin n) R) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b)
    (hc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ a i j)
    (hu : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, ρ (a ^ l ^ e) = 1)
    (z : G.G₀ → Matrix (Fin n) (Fin n) R) (hzc : ∀ i j, AdicCont (Ideal.span {t}) fun a => z a i j)
    (hz : ∀ a b, z (a * b) = z a + ρ (h.p₀ a) * z b * ρ (h.p₀ a⁻¹)) :
    ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) R, z = fun a => z' (g.p₀ a) := by
  obtain ⟨N, hN⟩ := ht
  have hI : Ideal.span {t} ^ N = ⊥ := by
    rw [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]
  have hle' : H.comap h.p ≤ G.η.ker := fun a ha => by
    rw [MonoidHom.mem_ker, ← h.η a]
    exact hle ha
  have hmul : ∀ a b : G.G₀, ρ (h.p₀ (a * b)) = ρ (h.p₀ a) * ρ (h.p₀ b) := fun a b => by
    rw [map_mul, hm]
  have hρc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ (h.p₀ a) i j := fun i j =>
    (h.adicCont_iff _ (fun c => ρ c i j)).2 (hc i j)
  have hun : ∀ (m : ℕ) (k : G.G₀), (k : G.Γ) ∈ H.comap h.p →
      ∃ e, ∀ i j, (ρ (h.p₀ (k ^ l ^ e)) - 1) i j ∈ Ideal.span {t} ^ m := by
    intro m k hk'
    obtain ⟨e, he⟩ := hu (h.p₀ k) hk'
    exact ⟨e, fun i j => by rw [map_pow, he, sub_self]; exact Submodule.zero_mem _⟩
  have hcoc := (coc_pl l L G n R (Ideal.span {t}) (fun a => ρ (h.p₀ a)) z (H.comap h.p)
    (ho.preimage h.cont) hle' hl (by simp [h1]) hmul hρc hun hzc hz).2
  have hzero : ∀ k : G.G₀, g.p₀ k = 1 → z k = 0 := by
    intro k hk1
    have hmem : (k : G.Γ) ∈ PL l (H.comap h.p) := by
      rw [← hk, MonoidHom.mem_ker]
      exact congrArg Subtype.val hk1
    ext i j
    have hz0 := (hcoc k hmem N i j).2
    rw [hI, Ideal.mem_bot] at hz0
    simpa using hz0
  refine ⟨fun c => z (Classical.choose (g.p₀_surj c)), funext fun a => ?_⟩
  obtain hb' := Classical.choose_spec (g.p₀_surj (g.p₀ a))
  show z a = z (Classical.choose (g.p₀_surj (g.p₀ a)))
  generalize Classical.choose (g.p₀_surj (g.p₀ a)) = b at hb' ⊢
  have hk1 : g.p₀ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hb', inv_mul_cancel]
  have hab : b = a * (a⁻¹ * b) := by group
  rw [hab, hz, hzero _ hk1]
  simp

private theorem UpperTheory.V.Pa.sel_desc_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (m : ℕ)
    (X : Type) [CommRing X] [Algebra x.A X] (hX : algebraMap x.A X (x.t ^ m) = 0) (a : F.G₀)
    (ha : ∀ i j, (mat x.ρ a - 1) i j ∈ Ideal.span {x.t ^ m}) : x.ρX X a = 1 := by
  ext i j
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha i j)
  have h0 : algebraMap x.A X ((mat x.ρ a - 1) i j) = 0 := by
    rw [← hc, map_mul, hX, mul_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  simp only [NP.ρX, Matrix.map_apply]
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem UpperTheory.V.Pa.epM_mul_self_eq_zero (X : Type) [CommRing X] (g n : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  apply DD.ext
  · show (0 : X) * 0 = 0
    simp
  · show (fun r => (0 : X) * Z r c j + Z r i c * 0) = 0
    funext r
    simp
  · show (fun r => (0 : X) * (0 : Fin g → X) r + (0 : Fin g → X) r * 0) = 0
    funext r
    simp
  · show (0 : X) * 0 + 0 * 0 + ∑ r, (Z r i c * (0 : Fin g → X) r + (0 : Fin g → X) r * Z r c j) = 0
    simp

theorem UpperTheory.V.Pa.sel_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' G0 : Glob l L) (g : G.Hom G') (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (H : Subgroup G0.Γ) [H.Normal] (m : ℕ), IsOpen (H : Set G0.Γ) → H ≤ G0.η.ker → x.UnipOn H → g.p.ker = PL l (H.comap h.p) → (∀ z ∈ SelP h x (x.Am m), ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (x.Am m), z = fun a => z' (g.p₀ a)) ∧ ∀ z ∈ Sel1 h (x.Am m) k ∪ Sel2 h (x.Am m) k, ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g), z = fun a => z' (g.p₀ a) := by
  intro l _ L G G' G0 g h n x k H _ m ho hle hU hk
  obtain ⟨_, _, hnil1, hnil2, hl0, _⟩ := am_fin l G0.frame n x m k.g
  have hrho := rho_hom l G0.frame n x k (x.Am m)
  have hX0 : algebraMap x.A (x.Am m) (x.t ^ m) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)
  have hl1 : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)) l, hl0, map_zero]
  have hlD : (l : DD (x.Am m) k.g) = 0 := by
    rw [← map_natCast (algebraMap x.A (DD (x.Am m) k.g)) l, hl0, map_zero]
  constructor
  · intro z hz
    obtain ⟨_, hzc, hzm, _⟩ := hz
    refine sel_desc_fac g h (algebraMap x.A (x.Am m) x.t) hnil1 hl1 H ho hle hk (x.ρX (x.Am m))
      hrho.1.1 hrho.1.2.1 hrho.1.2.2 ?_ z hzc hzm
    intro a ha
    obtain ⟨e, he⟩ := hU m a ha
    exact ⟨e, sel_desc_one x m (x.Am m) hX0 _ he⟩
  · have hu2 : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, k.ρ1 (x.Am m) (a ^ l ^ e) = 1 := by
      intro a ha
      obtain ⟨e, he⟩ := hU m a ha
      have hX : algebraMap x.A (DD (x.Am m) k.g) (x.t ^ m) = 0 := by
        show DD.C (algebraMap x.A (x.Am m) (x.t ^ m)) = 0
        rw [hX0, map_zero]
      have h1 := sel_desc_one x m (DD (x.Am m) k.g) hX _ he
      let φ : G0.G₀ →* Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) :=
        { toFun := k.ρ1 (x.Am m), map_one' := hrho.2.1.1, map_mul' := hrho.2.1.2.1 }
      have hp : ∀ (b : G0.G₀) (N : ℕ), k.ρ1 (x.Am m) (b ^ N) = k.ρ1 (x.Am m) b ^ N :=
        fun b N => map_pow φ b N
      refine ⟨e + 1, ?_⟩
      rw [pow_succ, pow_mul, hp, Kap.ρ1, h1, mul_one]
      have hE := epM_mul_self_eq_zero (x.Am m) k.g n (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m)))
      generalize DD.epM (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m))) = E at hE ⊢
      have hN : ∀ N : ℕ, (1 + E) ^ N = 1 + N • E := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_zero,
            add_zero, succ_nsmul]
          abel
      rw [hN]
      have hlE : l • E = 0 := Matrix.ext fun i j => by
        rw [Matrix.smul_apply, nsmul_eq_mul, hlD, zero_mul, Matrix.zero_apply]
      rw [hlE, add_zero]
    intro z hz
    rcases hz with hz | hz <;> obtain ⟨_, hzc, hzm, _⟩ := hz <;>
      exact sel_desc_fac g h (algebraMap x.A (DD (x.Am m) k.g) x.t) hnil2 hlD H ho hle hk
        (k.ρ1 (x.Am m)) hrho.2.1.1 hrho.2.1.2.1 hrho.2.1.2.2 hu2 z hzc hzm
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private def stabR {P Z : Type} [Group P] (c : P → Z) : Subgroup P where
  carrier := {k | ∀ g, c (g * k) = c g}
  one_mem' g := by rw [mul_one]
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha g := by
    have := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

private theorem stabR_open {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (c : P → Z) (hc : IsLocallyConstant c) : IsOpen (stabR c : Set P) := by
  classical
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have key : ∀ z ∈ Set.range c, ∀ᶠ k in nhds (1 : P), ∀ g, c g = z → c (g * k) = z := by
    intro z _
    have hK : IsCompact (c ⁻¹' {z}) := (hc.isClosed_fiber z).isCompact
    obtain ⟨V, hV, hKV⟩ := compact_open_separated_mul_right hK (hc.isOpen_fiber z) le_rfl
    filter_upwards [hV] with k hk g hg
    exact hKV (Set.mul_mem_mul hg hk)
  have hall := (Filter.eventually_all_finite hc.range_finite).2 key
  filter_upwards [hall] with k hk
  exact (show ∀ g, c (g * k) = c g from fun g => hk (c g) ⟨g, rfl⟩ g rfl)

private theorem fac_iff {P A Z : Type} [Group P] [Group A] (f : P →* A) (hf : Function.Surjective f) (c : P → Z) :
    (∃ z : A → Z, ∀ g, z (f g) = c g) ↔ f.ker ≤ stabR c := by
  constructor
  · rintro ⟨z, hz⟩ k hk
    show ∀ g, c (g * k) = c g
    intro g
    rw [← hz, ← hz, map_mul, MonoidHom.mem_ker.1 hk, mul_one]
  · intro hle
    refine ⟨fun a => c (Classical.choose (hf a)), fun g => ?_⟩
    show c (Classical.choose (hf (f g))) = c g
    have hspec : f (Classical.choose (hf (f g))) = f g := Classical.choose_spec (hf (f g))
    generalize Classical.choose (hf (f g)) = g' at hspec ⊢
    have hk : g'⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hspec, inv_mul_cancel]
    have := (show ∀ y, c (y * (g'⁻¹ * g)) = c y from hle hk) g'
    rw [mul_inv_cancel_left] at this
    exact this.symm

private theorem ker_iff {P A : Type} [Group P] [Group A] (H : Subgroup P) (B : Subgroup A) (π : P →* A)
    (f : H →* B) (hf : ∀ g, (f g : A) = π g) (hH : π.ker ≤ H) (S : Subgroup H) :
    f.ker ≤ S ↔ π.ker ≤ (S.map H.subtype).normalCore := by
  have hker : ∀ h : H, h ∈ f.ker ↔ (h : P) ∈ π.ker := by
    intro h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hf, OneMemClass.coe_eq_one]
  constructor
  · intro hle
    rw [Subgroup.normal_le_normalCore]
    intro k hk
    have hkH : k ∈ H := hH hk
    exact ⟨⟨k, hkH⟩, hle ((hker ⟨k, hkH⟩).2 hk), rfl⟩
  · intro hle h hh
    obtain ⟨s, hs, hsh⟩ := (Subgroup.normalCore_le _) (hle ((hker h).1 hh))
    have : s = h := Subtype.ext hsh
    rw [← this]
    exact hs

theorem UpperTheory.V.Pa.eventually_factor_through_tower_iff_limit :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ((∃ zN : (T.GN N).G₀ → Z, ∀ g, zN (Λ.π0 N g) = c g) ↔ ∃ z : Λ.G.G₀ → Z, ∀ g, z (Λ.πo0 g) = c g) := by
  intro l _ L G0 T Λ Z c hc
  set K0 : Subgroup Λ.Ph := (Λ.G.η.comp Λ.πo).ker with hK0def
  have hK0 : IsOpen (K0 : Set Λ.Ph) := Λ.Ph0_open
  haveI : CompactSpace Λ.Ph0 := isCompact_iff_compactSpace.mp (K0.isClosed_of_isOpen hK0).isCompact
  have hS : IsOpen (stabR c : Set Λ.Ph0) := stabR_open c hc
  have hO : IsOpen (((stabR c).map K0.subtype : Subgroup Λ.Ph) : Set Λ.Ph) := by
    rw [Subgroup.coe_map]
    exact hK0.isOpenMap_subtype_val _ hS
  let O : OpenSubgroup Λ.Ph := ⟨(stabR c).map K0.subtype, hO⟩
  haveI : Finite (Λ.Ph ⧸ O.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hO
  haveI : O.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let V : OpenNormalSubgroup Λ.Ph :=
    { toSubgroup := O.toSubgroup.normalCore
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.toSubgroup.normalCore_isClosed O.isClosed) }
  have hHo : Λ.πo.ker ≤ K0 := by
    intro k hk
    rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  filter_upwards [Λ.ker_lim V] with N hN
  have hHN : (Λ.π N).ker ≤ K0 := by
    intro k hk
    rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Λ.η_π N, MonoidHom.mem_ker.1 hk, map_one]
  rw [fac_iff _ (Λ.π0_surj N), fac_iff _ Λ.πo0_surj,
    ker_iff K0 _ (Λ.π N) (Λ.π0 N) (fun g => rfl) hHN, ker_iff K0 _ Λ.πo Λ.πo0 (fun g => rfl) hHo]
  have e : (Λ.π N).ker ⊔ ((stabR c).map K0.subtype).normalCore =
      Λ.πo.ker ⊔ ((stabR c).map K0.subtype).normalCore := hN
  rw [← sup_eq_right, e, sup_eq_right]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.eventually_locallyConstant_comp_tower_eq :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (ρ : G0.G₀ → Z), IsLocallyConstant ρ → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ g, ρ ((T.h N).p₀ (Λ.π0 N g)) = ρ (Λ.h.p₀ (Λ.πo0 g)) := by
  intro l _ L G0 T Λ Z ρ hρ
  have hKo : IsOpen ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := G0.η_open
  have hKc : IsClosed ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := Subgroup.isClosed_of_isOpen _ hKo
  haveI : CompactSpace G0.G₀ := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range ρ).Finite := hρ.range_finite
  have hS : ∀ z, ∃ V ∈ nhds (1 : G0.Γ), ∀ v ∈ V, ∀ x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ),
      v * x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) := by
    intro z
    have hc : IsCompact (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      (hρ.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      hKo.isOpenMap_subtype_val _ (hρ.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hc ho subset_rfl
    open scoped Pointwise in
    exact ⟨V, hV, fun v hv x hx => hVS (Set.mul_mem_mul hv hx)⟩
  choose V hV hVS using hS
  have hW : (⋂ z ∈ Set.range ρ, V z) ∈ nhds (1 : G0.Γ) := (Filter.biInter_mem hfin).2 fun z _ => hV z
  obtain ⟨O, hOW, hOo, h1O⟩ := mem_nhds_iff.1 hW
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  refine (Λ.p_lim H).mono ?_
  intro N hN g
  set a := (T.h N).p₀ (Λ.π0 N g)
  set b := Λ.h.p₀ (Λ.πo0 g)
  have hab : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ (H : Set G0.Γ) := hN g.1
  have h1 : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ V (ρ b) := Set.mem_iInter₂.1 (hOW (hH hab)) (ρ b) ⟨b, rfl⟩
  have h2 : (b : G0.Γ) ∈ Subtype.val '' (ρ ⁻¹' {ρ b}) := ⟨b, rfl, rfl⟩
  have h3 := hVS (ρ b) _ h1 _ h2
  rw [inv_mul_cancel_right] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = a := Subtype.ext he
  rw [← e]
  exact ha'
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ms_single {B X Y : Type} [CommRing B] [Group X] [Group Y] (f : X →* Y) (a : X) (c : B) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

private theorem ms_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a : F.G₀) (c : B) :
    F.star O B n (MonoidAlgebra.single a c) =
      MonoidAlgebra.single (F.conj a)⁻¹ (c * ((F.eps O B a ^ (1 - (n : ℤ)) : Bˣ) : B)) := by
  unfold GFrame.star GFrame.starOp
  rw [MonoidAlgebra.lift_single, MulOpposite.unop_smul]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, MonoidAlgebra.smul_single, smul_eq_mul]

private theorem ms_add {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a b : MonoidAlgebra B F.G₀) :
    F.star O B n (a + b) = F.star O B n a + F.star O B n b := by
  unfold GFrame.star
  rw [map_add (f := _), MulOpposite.unop_add]

private theorem ms_zero {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) : F.star O B n 0 = 0 := by
  unfold GFrame.star
  rw [map_zero, MulOpposite.unop_zero]

theorem UpperTheory.V.Pa.map_star :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B], (∀ y, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.star O B n y) = G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B g.p₀ y)) ∧ (∀ v (ψ : Fin n → L.Gv v →* Bˣ) a, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.oEl v ψ a) = G'.frame.oEl v ψ a) ∧ (∀ (ph : G.G₀) (U : Fin n → B), MonoidAlgebra.mapDomainRingHom B g.p₀ (q1El ph U) = q1El (g.p₀ ph) U) ∧ ∀ (ph ta : G.G₀) (U : Fin n → B) i y, MonoidAlgebra.mapDomainRingHom B g.p₀ (q2El ph ta U i y) = q2El (g.p₀ ph) (g.p₀ ta) U i y := by
  intro l _ L G G' g n O _ _ B _ _
  refine ⟨fun y => ?_, fun v ψ a => ?_, fun ph U => ?_, fun ph ta U i y => ?_⟩
  · induction y using MonoidAlgebra.induction_linear with
    | zero => rw [ms_zero, map_zero, ms_zero]
    | add a b ha hb => rw [ms_add, map_add (f := _), map_add (f := _), ms_add, ha, hb]
    | single a c =>
      rw [ms_star, ms_single, ms_single, ms_star, map_inv, g.p₀_conj, g.eps_p₀]
  · unfold GFrame.oEl
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one, g.p₀_φ]
  · unfold q1El
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one]
  · unfold q2El
    rw [map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2
      funext k
      simp only [Function.comp_apply]
      split_ifs
      · exact map_one _
      · simp only [map_sub, ms_single, map_one]
    · simp only [map_sub, ms_single, map_one]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem gdesc_ker {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) (J : TwoSidedIdeal (MonoidAlgebra A G))
    (hJ : ∀ k, f k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J) (x : MonoidAlgebra A G)
    (hx : MonoidAlgebra.mapDomainAlgHom A A f x = 0) : x ∈ J := by
  have key : ∀ y : MonoidAlgebra A G,
      y - MonoidAlgebra.mapDomain (Function.surjInv hf) (MonoidAlgebra.mapDomainAlgHom A A f y) ∈ J := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g a =>
      have h1 := J.mul_mem_left (MonoidAlgebra.single (Function.surjInv hf (f g)) a) _
        (hJ ((Function.surjInv hf (f g))⁻¹ * g) (by simp [Function.surjInv_eq]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_inv_cancel_left, mul_one, mul_one] at h1
      simpa using h1
  simpa [hx] using key x

private theorem gdesc_toT {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G) :
    toT A G' B (MonoidAlgebra.mapDomainRingHom B f x) =
      Algebra.TensorProduct.map (AlgHom.id B B) (MonoidAlgebra.mapDomainAlgHom A A f) (toT A G B x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s => simp [toT_single]

theorem UpperTheory.V.Pa.gdet_desc :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G), Function.Surjective f → (∀ k, f k = 1 → D.Kills (MonoidAlgebra.single k 1 - 1)) → ∃ D' : GDet n A G', D'.comap f = D := by
  intro n A G G' _ _ _ f D hf hk
  have hs : Function.Surjective (MonoidAlgebra.mapDomainAlgHom A A f) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | single g a =>
      obtain ⟨g, rfl⟩ := hf g
      exact ⟨MonoidAlgebra.single g a, by simp⟩
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D.toDet (MonoidAlgebra.mapDomainAlgHom A A f) hs
    (gdesc_ker f hf _ fun k h => (UpperTheory.V.CA.d_ker _ _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hk k h)))
  refine ⟨GDet.ofDet D', ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  exact GDet.ext fun B _ _ x => congrArg (D'.D B) (gdesc_toT f B x)
end
