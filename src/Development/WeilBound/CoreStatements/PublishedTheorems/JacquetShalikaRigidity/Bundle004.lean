module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BlockMirrorMap

theorem blk_mono {R : Type} [CommRing R] {a i j : ℕ} (hij : i ≤ j) {c : GL (Fin a) R} (h : GlobalTheory i c) : GlobalTheory j c :=
  fun p q hpq => h p q (by omega)

theorem blk_mul {R : Type} [CommRing R] {a j : ℕ} {c c' : GL (Fin a) R} (hc : GlobalTheory j c) (hc' : GlobalTheory j c') :
    GlobalTheory j (c * c') := by
  intro p q hpq
  rw [Units.val_mul]
  rcases hpq with h | h
  · calc (c.val * c'.val) p q = ((1 : Matrix (Fin a) (Fin a) R) * c'.val) p q := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun s _ => by rw [hc p s (Or.inl h)]
      _ = _ := by rw [Matrix.one_mul]; exact hc' p q (Or.inl h)
  · calc (c.val * c'.val) p q = (c.val * (1 : Matrix (Fin a) (Fin a) R)) p q := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun s _ => by rw [hc' s q (Or.inr h)]
      _ = _ := by rw [Matrix.mul_one]; exact hc p q (Or.inr h)

theorem mir_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {a m : ℕ} {g : GL (Fin a) R}
    (h : Mir m g) : Mir m (GeneralLinearGroup.map f g) := by
  intro p q hpq
  show f (g.val p q) = _
  rw [h p q hpq, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem grow {G X : Type} [TopologicalSpace G] [MulOneClass G] [ContinuousMul G] {Q : X → Prop}
    {bl bi : G → Prop} {B B' : Set G → X → Prop}
    (hbl : ∀ a b, bl a → bl b → bl (a * b)) (hi : ∀ c, bi c → bl c)
    (h : ∀ U ∈ 𝓝 (1 : G), ∃ x C, C ⊆ U ∧ Q x ∧ (∀ c ∈ C, bl c) ∧ B C x)
    (hs : ∀ U ∈ 𝓝 (1 : G), ∀ x C, Q x → B C x →
      ∃ x' C₀, C₀ ⊆ U ∧ Q x' ∧ (∀ c ∈ C₀, bi c) ∧ B' (Set.image2 (· * ·) C C₀) x') :
    ∀ U ∈ 𝓝 (1 : G), ∃ x C, C ⊆ U ∧ Q x ∧ (∀ c ∈ C, bl c) ∧ B' C x := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := exists_nhds_one_split hU
  obtain ⟨x, C, hCV, hQ, hbC, hB⟩ := h V hV
  obtain ⟨x', C₀, hC₀V, hQ', hb₀, hB'⟩ := hs V hV x C hQ hB
  refine ⟨x', Set.image2 (· * ·) C C₀, ?_, hQ', ?_, hB'⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hVU a (hCV ha) b (hC₀V hb)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hbl a b (hbC a ha) (hi b (hb₀ b hb))

end BlockMirrorMap

theorem kept_block_at_of_pair_level_chain_threshold : jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → InfinitePlaceStep → FinitePlaceStep → K4 := by
  classical
  intro hS10 hG0 h4a h4b E _ _ _ k wt ρ J hW ψ hψ S Y hY j hj U hU x hxY hxS hxL h1
  have ins1 : InS S (1 : GA E k) := fun v _ => map_one _
  have uu1 : UU 0 (1 : GA E k) :=
    ⟨fun p q h => by rw [Units.val_one, Matrix.one_apply_ne (ne_of_lt h).symm], fun p => by simp,
      fun p q _ => rfl⟩
  have ps1 : psN ψ (1 : GA E k) = 1 := by
    have e : (∑ p : Fin k × Fin k with (p.2 : ℕ) = p.1 + 1, (1 : GA E k).val p.1 p.2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Units.val_one, Matrix.one_apply_ne]
      intro h
      rw [h] at hp
      omega
    unfold psN
    rw [e, AddChar.map_zero_eq_one]
  have om0 : ∀ g : GA E k, Om 0 0 g → g = 1 := by
    intro g hg
    apply (hG0 E k).2.2.2.2.2.1
    · rw [(hS10 _ k 0).2.1 _ hg.1, map_one]
    · intro v
      rw [(hS10 _ k 0).2.1 _ (hg.2 v), map_one]
  have start : Bump ψ S (Om 0 0) {1} (Wh ψ (J x)) := by
    refine ⟨isCompact_singleton, ?_, ⟨1, one_pos, by rw [h1]; simp⟩, ?_⟩
    · intro c hc
      rw [Set.mem_singleton_iff.mp hc]
      exact ins1
    · intro g hg _
      obtain rfl := om0 g hg
      exact ⟨1, 1, rfl, 1, uu1, ins1, (mul_one 1).symm, zero_le_one, by rw [h1, ps1]; simp⟩
  let P : ℕ → (Pl E → ℕ) → Prop := fun n m => ∀ V ∈ 𝓝 (1 : GA E k), ∃ x' C, C ⊆ V ∧
    (J x' ∈ Y ∧ SmV (ρ.comp (infGL E k)) x' ∧ Lev S (J x')) ∧ (∀ c ∈ C, GlobalTheory j c) ∧
      Bump ψ S (Om n m) C (Wh ψ (J x'))
  have p0 : P 0 0 := by
    intro V hV
    exact ⟨x, {1}, Set.singleton_subset_iff.mpr (mem_of_mem_nhds hV), ⟨hxY, hxS, hxL⟩,
      fun c hc => by rw [Set.mem_singleton_iff.mp hc]; exact (hS10 _ k j).2.2.2.1, start⟩
  have stepInf : ∀ n, n ≤ j → P n 0 := by
    intro n
    induction n with
    | zero => intro _; exact p0
    | succ n ih =>
      intro hn
      refine BlockMirrorMap.grow (fun a b ha hb => BlockMirrorMap.blk_mul ha hb) (fun c hc => BlockMirrorMap.blk_mono hn hc) (ih (by omega)) ?_
      intro V hV x C hQ hB
      obtain ⟨x', C₀, a, b, c, d, e, f⟩ :=
        h4a E k wt ρ J hW ψ hψ S Y hY n 0 (by omega) (fun _ _ => rfl) V hV x C hQ.1 hQ.2.1 hQ.2.2 hB
      exact ⟨x', C₀, a, ⟨b, c, d⟩, e, f⟩
  have stepFin : ∀ (v : Pl E), v ∈ S → ∀ m : Pl E → ℕ, m v = 0 → (∀ u, u ∉ S → m u = 0) → P j m →
      ∀ i, i ≤ j → P j (Function.update m v i) := by
    intro v hv m hmv hm hP i
    induction i with
    | zero => intro _; rw [Function.update_eq_self_iff.mpr hmv.symm]; exact hP
    | succ i ih =>
      intro hi
      have supp : ∀ u, u ∉ S → Function.update m v i u = 0 := by
        intro u hu
        have hne : u ≠ v := fun h => hu (h ▸ hv)
        rw [Function.update_of_ne hne]
        exact hm u hu
      refine BlockMirrorMap.grow (bi := fun c => GlobalTheory (Function.update m v i v + 1) c) (fun a b ha hb => BlockMirrorMap.blk_mul ha hb)
        (fun c hc => BlockMirrorMap.blk_mono (by simp; omega) hc) (ih (by omega)) ?_
      intro V hV x C hQ hB
      obtain ⟨x', C₀, a, b, c, d, e, f⟩ :=
        h4b E k wt ρ J hW ψ hψ S Y hY j (Function.update m v i) v hv (by simp; omega) supp V hV x C
          hQ.1 hQ.2.1 hQ.2.2 hB
      simp only [Function.update_self, Function.update_idem] at f
      exact ⟨x', C₀, a, ⟨b, c, d⟩, e, f⟩
  have key : ∀ T : Finset (Pl E), T ⊆ S → P j (fun w => if w ∈ T then j else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      have e : (fun w : Pl E => if w ∈ (∅ : Finset (Pl E)) then j else 0) = 0 := by
        funext w
        simp
      rw [e]
      exact stepInf j le_rfl
    · intro v T hv ih hT
      have h := stepFin v (hT (Finset.mem_insert_self v T)) (fun w => if w ∈ T then j else 0)
        (by simp [hv]) (fun u hu => by simp [show u ∉ T from fun h => hu (hT (Finset.mem_insert_of_mem h))])
        (ih (subset_trans (Finset.subset_insert v T) hT)) j le_rfl
      convert h using 1
      funext w
      by_cases hw : w = v
      · subst hw; simp
      · simp [hw]
  obtain ⟨x', C, hCU, ⟨hY', hS', hL'⟩, hbl, hB⟩ := key S subset_rfl U hU
  refine ⟨x', C, hCU, hY', hS', hL', hbl, hB.1, hB.2.1, hB.2.2.1, fun g hg hW0 => hB.2.2.2 g ?_ hW0⟩
  refine ⟨BlockMirrorMap.mir_map _ hg.2, fun v => ?_⟩
  by_cases hv : v ∈ S
  · simp only [hv, if_true]
    exact BlockMirrorMap.mir_map _ hg.2
  · simp only [hv, if_false]
    rw [hg.1 v hv]
    exact (hS10 _ k 0).2.2.1

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace TorusPowerExponential

section Loc

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)

theorem torusPow_add (x y : Fin n → ℤ) :
    Iwasawa.torusPow F n (x + y) = Iwasawa.torusPow F n x * Iwasawa.torusPow F n y := by
  simp only [Iwasawa.torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem conj_mem (x : Fin n → ℤ) {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹ ∈ Iwasawa.unipotent F n :=
  Iwasawa.diagGL_mul_mul_inv_mem_unipotent F n hu _

theorem exp_torus_mul (x : Fin n → ℤ) (h : GL (Fin n) F) :
    Iwasawa.iwasawaExponent F n (Iwasawa.torusPow F n x * h) = x + Iwasawa.iwasawaExponent F n h := by
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent F n h
  have key : Iwasawa.torusPow F n x * h = (Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹) *
      Iwasawa.torusPow F n (x + Iwasawa.iwasawaExponent F n h) * κ := by
    rw [torusPow_add]
    conv_lhs => rw [e]
    group
  rw [key, Iwasawa.iwasawaExponent_eq F n (conj_mem F n x hu) hκ]

theorem torusPow_zero : Iwasawa.torusPow F n 0 = 1 := by
  simpa using torusPow_add F n 0 0

end Loc

section Glob

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countable_pl : Countable (Pl E) := by
  classical
  haveI : Countable (𝓞 E) := (RingOfIntegers.basis E).repr.toEquiv.injective.countable
  let f : Pl E → Finset (𝓞 E) := fun v ↦ (IsNoetherian.noetherian v.asIdeal).choose
  refine Function.Injective.countable (f := f) fun v w h ↦ ?_
  have hv := (IsNoetherian.noetherian v.asIdeal).choose_spec
  have hw := (IsNoetherian.noetherian w.asIdeal).choose_spec
  ext1
  rw [← hv, ← hw]
  exact congrArg (fun s : Finset (𝓞 E) ↦ Submodule.span (𝓞 E) (s : Set (𝓞 E))) h

def A (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) : Set (GA E k) :=
  {g | ∀ w : Off E S, Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w}

theorem A_zero (S : Finset (Pl E)) : A (k := k) S 0 = G0 S := by
  ext g
  simp only [A, G0, Set.mem_setOf_eq, Finsupp.coe_zero, Pi.zero_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

theorem A_cover (S : Finset (Pl E))
    (hfin : ∀ g : GA E k, {w | Iwasawa.iwasawaExponent _ k (cLoc w g) ≠ 0}.Finite) (g : GA E k) :
    ∃ l, g ∈ A S l :=
  ⟨Finsupp.ofSupportFinite (fun w : Off E S => Iwasawa.iwasawaExponent _ k (cLoc w.1 g))
    ((hfin g).preimage Subtype.val_injective.injOn), fun w => rfl⟩

theorem A_disj (S : Finset (Pl E)) : Pairwise (Function.onFun Disjoint (A (k := k) S)) := by
  intro l l' hne
  exact Set.disjoint_left.2 fun g h h' => hne (Finsupp.ext fun w => (h w).symm.trans (h' w))

theorem A_closed (S : Finset (Pl E))
    (hcl : ∀ (w : Pl E) (l : Fin k → ℤ), IsClopen {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w g) = l})
    (l : Off E S →₀ (Fin k → ℤ)) : IsClosed (A S l) := by
  have : A S l = ⋂ w : Off E S, {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w} := by
    ext; simp [A]
  rw [this]
  exact isClosed_iInter fun w => (hcl w.1 (l w)).isClosed

theorem cLoc_unip (u : GA E k) (hu : UU 0 u) (w : Pl E) : cLoc w u ∈ Iwasawa.unipotent _ k := by
  refine ⟨fun i c hci => ?_, fun i => ?_⟩
  · change ((pLoc E w).comp (pFin E)) (u.val i c) = 0
    rw [hu.1 i c hci, map_zero]
  · change ((pLoc E w).comp (pFin E)) (u.val i i) = 1
    rw [hu.2.1 i, map_one]

theorem A_mul (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) (u g : GA E k) (hu : UU 0 u) :
    u * g ∈ A S l ↔ g ∈ A S l := by
  have h := fun w : Pl E => Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ k (cLoc_unip u hu w) (cLoc w g)
  simp only [A, Set.mem_setOf_eq, map_mul, h]

theorem A_tr (S : Finset (Pl E))
    (hloc : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), cLoc w (fl k w u : GA E k) = u)
    (hoff : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → cLoc v (fl k w u : GA E k) = 1)
    (l : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (hw : l w = 0) (x : Fin k → ℤ) (g : GA E k) :
    fl k w.1 (Iwasawa.torusPow _ k x) * g ∈ A S (Finsupp.single w x + l) ↔ g ∈ A S l := by
  simp only [A, Set.mem_setOf_eq, map_mul]
  have key : ∀ v : Off E S, (Iwasawa.iwasawaExponent _ k (cLoc v.1 (fl k w.1 (Iwasawa.torusPow _ k x)) *
      cLoc v.1 g) = (Finsupp.single w x + l) v ↔ Iwasawa.iwasawaExponent _ k (cLoc v.1 g) = l v) := by
    intro v
    by_cases hv : v = w
    · subst hv
      rw [hloc, exp_torus_mul, Finsupp.add_apply, Finsupp.single_eq_same, hw, add_zero]
      constructor
      · intro h; simpa using h
      · intro h; rw [h, add_zero]
    · have e1 : (Finsupp.single w x + l) v = l v := by simp [Finsupp.single_apply, Ne.symm hv]
      rw [hoff w.1 v.1 _ (fun h => hv (Subtype.ext h)), one_mul, e1]
  exact forall_congr' key

theorem Phi_tr (S : Finset (Pl E)) (Φ : GA E k → ℂ) (a : Off E S → (Fin k → ℤ) → ℂ) (hlaw : LawOff S Φ a)
    (ha0 : ∀ w, a w 0 = 1)
    (hcomm : ∀ (w : Pl E) (g : GA E k), cLoc w g = 1 → ∀ u, g * fl k w u = fl k w u * g)
    (hdec : ∀ (w : Pl E) (g : GA E k), ∃ g' : GA E k, cLoc w g' = 1 ∧ g = g' * fl k w (cLoc w g))
    (w : Off E S) (x : Fin k → ℤ) (g : GA E k) (hg : Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = 0) :
    Φ (fl k w.1 (Iwasawa.torusPow _ k x) * g) = a w x * Φ g := by
  obtain ⟨g', h1, hg'⟩ := hdec w.1 g
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent _ k (cLoc w.1 g)
  rw [hg] at e
  have h0 : Φ g = Φ g' := by
    rw [hg', e, hlaw w g' h1 u hu κ hκ 0, ha0, mul_one]
  have h2 : fl k w.1 (Iwasawa.torusPow _ k x) * g = g' * fl k w.1
      ((Iwasawa.torusPow _ k x * u * (Iwasawa.torusPow _ k x)⁻¹) * Iwasawa.torusPow _ k x * κ) := by
    conv_lhs => rw [hg', e]
    rw [← mul_assoc, ← hcomm w.1 g' h1, mul_assoc, ← map_mul, torusPow_zero, mul_one]
    congr 2
    group
  rw [h2, hlaw w g' h1 _ (conj_mem _ k x hu) κ hκ x, h0, mul_comm]

end Glob

end TorusPowerExponential

theorem torus_exponential_of_open : jumpWindows.G0 → C0 → C1 → C2 := by
  intro hG hC0 hC1 E _ _ _ k μ _ hk β hβ S Φ a hΦm hΦu hlaw ha0 hint
  obtain ⟨-, -, -, hloc, hoff, -, -, hcomm, -⟩ := hG E k
  obtain ⟨-, -, -, -, hfin, hcl, hdec⟩ := hC0 E k S
  haveI := TorusPowerExponential.countable_pl (E := E)
  have hmeas : ∀ l, MeasurableSet (TorusPowerExponential.A (k := k) S l) := fun l => (TorusPowerExponential.A_closed S hcl l).measurableSet
  let c : Off E S → (Fin k → ℤ) → ℂ := fun w x => (nq w : ℂ) ^ rhoPair x * a w x
  have hc0 : ∀ w, c w 0 = 1 := fun w => by simp [c, rhoPair, ha0]
  have hstep : ∀ (f : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (x : Fin k → ℤ), f w = 0 →
      ∫ g in TorusPowerExponential.A S (Finsupp.single w x + f), Φ g ∂μ.withDensity β =
        c w x * ∫ g in TorusPowerExponential.A S f, Φ g ∂μ.withDensity β := by
    intro f w x hw
    have hUU : ∀ u, UU 0 u → ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ (u * g) =
        (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ g := by
      intro u hu g
      by_cases hg : g ∈ TorusPowerExponential.A S (Finsupp.single w x + f)
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_mul S _ u g hu).2 hg), Set.indicator_of_mem hg, hΦu u hu g]
      · rw [Set.indicator_of_notMem (mt (TorusPowerExponential.A_mul S _ u g hu).1 hg), Set.indicator_of_notMem hg]
    obtain ⟨-, hE⟩ := hC1 E k μ hk β hβ w.1 x ((TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ)
      (hΦm.indicator (hmeas _))
      hUU
      (hint.indicator (hmeas _))
    rw [← integral_indicator (hmeas _), hE, ← integral_indicator (hmeas _)]
    have hpt : ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ
        (fl k w.1 (Iwasawa.torusPow (w.1.adicCompletion E) k x) * g) =
        a w x * (TorusPowerExponential.A S f).indicator Φ g := by
      intro g
      by_cases hg : g ∈ TorusPowerExponential.A S f
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).2 hg), Set.indicator_of_mem hg,
          TorusPowerExponential.Phi_tr S Φ a hlaw ha0 hcomm (fun w g => (hdec w g).imp fun g' h => ⟨h.1, h.2.1⟩) w x g
            ((hg w).trans hw)]
      · rw [Set.indicator_of_notMem (fun h => hg ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).1 h)),
          Set.indicator_of_notMem hg, mul_zero]
    simp only [hpt, c, nq]
    rw [integral_const_mul, mul_assoc]
  have hclaim : ∀ l : Off E S →₀ (Fin k → ℤ), ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β =
      (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β := by
    intro l
    induction l using Finsupp.induction with
    | zero => simp [TorusPowerExponential.A_zero]
    | single_add w x f hwf hx ih =>
      have hfw : f w = 0 := Finsupp.notMem_support_iff.1 hwf
      change _ = Finsupp.prod (Finsupp.single w x + f) c * _
      change _ = Finsupp.prod f c * _ at ih
      have hdisj : Disjoint (Finsupp.single w x).support f.support := by
        refine Finset.disjoint_left.2 fun v hv hv' => hwf ?_
        rw [Finsupp.support_single_ne_zero _ hx, Finset.mem_singleton] at hv
        exact hv ▸ hv'
      rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (hc0 w), hstep f w x hfw, ih]
      simp only [c]
      ring
  have hU : ⋃ l, TorusPowerExponential.A (k := k) S l = Set.univ := Set.iUnion_eq_univ_iff.2 (TorusPowerExponential.A_cover S hfin)
  have hs := hasSum_integral_iUnion hmeas (TorusPowerExponential.A_disj S) hint.integrableOn
  rw [hU, setIntegral_univ] at hs
  have hfun : (fun l => ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β) =
      fun l : Off E S →₀ (Fin k → ℤ) => (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β :=
    funext hclaim
  rw [hfun] at hs
  exact hs

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace CosetIntegralMeasure

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem meas_mul (g : GA E k) : Measurable (fun h : GA E k => g * h) := by
  exact measurable_const_mul g

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  exact lintegral_map hF (meas_mul _)

end CosetIntegralMeasure

open CosetIntegralMeasure in
theorem coset_integration_of : N0 → N1 → N3 → CosetIntegralParabolic := by
  intro h0 _ _ E _ _ _ k j hj1 hjk F hF
  obtain ⟨hgam, huniq, hmul, hinv, -, hmir, -⟩ := h0 E k j hj1 hjk
  have hd : k - (j - 1 + 1) = k - j := by omega
  let f : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)) →
      ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) := fun x =>
    ⟨(gam x.1)⁻¹ * (x.2 : GL (Fin k) E), hmul (gam x.1)⁻¹ (x.2 : GL (Fin k) E) (hinv (gam x.1) (hgam x.1).1)
      (hmir (x.2 : GL (Fin k) E) x.2.2).2⟩
  have hinj : Function.Injective f := by
    rintro ⟨ξ, p⟩ ⟨ξ', p'⟩ h
    have hv : (gam ξ)⁻¹ * (p : GL (Fin k) E) = (gam ξ')⁻¹ * (p' : GL (Fin k) E) := congrArg Subtype.val h
    have hB : GlobalTheory j ((gam ξ)⁻¹ * (p : GL (Fin k) E))⁻¹ := hinv ((gam ξ)⁻¹ * (p : GL (Fin k) E)) (f (ξ, p)).2
    obtain ⟨q, -, huq⟩ := huniq _ hB
    have e1 : (ξ, (p : GL (Fin k) E)⁻¹) = q :=
      huq (ξ, (p : GL (Fin k) E)⁻¹) ⟨(hmir (p : GL (Fin k) E) p.2).1, by simp only [_root_.mul_inv_rev, inv_inv]⟩
    have e2 : (ξ', (p' : GL (Fin k) E)⁻¹) = q :=
      huq (ξ', (p' : GL (Fin k) E)⁻¹) ⟨(hmir (p' : GL (Fin k) E) p'.2).1, by simp only [hv, _root_.mul_inv_rev, inv_inv]⟩
    have h3 := Prod.mk.inj (e1.trans e2.symm)
    exact Prod.ext h3.1 (Subtype.ext (inv_injective h3.2))
  have hsurj : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    obtain ⟨⟨ξ, q⟩, ⟨hq, heq⟩, -⟩ := huniq γ⁻¹ (hinv γ hγ)
    have hq' : IsMir (j - 1) q := hq
    have heq' : γ⁻¹ = q * gam ξ := heq
    refine ⟨(ξ, ⟨q⁻¹, (hmir q hq').1⟩), Subtype.ext ?_⟩
    show (gam ξ)⁻¹ * q⁻¹ = γ
    rw [← _root_.mul_inv_rev, ← heq', inv_inv]
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hR : ∀ ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) =
      ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
        ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
    intro ξ
    have e0 := lint_nuG {γ : GL (Fin k) E | IsMir (j - 1) γ} (k - (j - 1 + 1))
      (fun h => F ((ratGL E k (gam ξ))⁻¹ * h)) (hF.comp (meas_mul _))
    refine e0.trans ?_
    rw [hd]
    refine tsum_congr fun p => ?_
    simp only [map_mul, map_inv, mul_assoc]
  calc ∫⁻ h, F h ∂nuB E k j
      = ∑' γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j) := lint_nuG {γ : GL (Fin k) E | GlobalTheory j γ} (k - j) F hF
    _ = ∑' x : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam x.1)⁻¹ * (x.2 : GL (Fin k) E)) * h) ∂nuD E k (k - j) :=
        (e.tsum_eq (fun γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) =>
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j))).symm
    _ = ∑' ξ : RowT E k j, ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
        exact ENNReal.tsum_prod (f := fun (ξ : RowT E k j) (p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E))) =>
            ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j))
    _ = ∑' ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) :=
        tsum_congr fun ξ => (hR ξ).symm

end PositivityTheory.AdelicQuotientData

end
end
