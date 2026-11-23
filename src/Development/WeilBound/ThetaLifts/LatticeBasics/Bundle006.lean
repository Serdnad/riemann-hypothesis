module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrthogonalGroupLemmas
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def idem (v : Pl F) : AF F := ((0, singleFin v 1) : Ainf F × Af F)

theorem ev_self (v : Pl F) : evFin F v (idem v) = 1 := evalV_singleFin_self v 1

theorem ev_ne {v u : Pl F} (h : u ≠ v) : evFin F u (idem v) = 0 := evalV_singleFin_ne h 1

theorem mul_idem {v : Pl F} {a : AF F} (h : evFin F v a = 0) : a * idem v = 0 := by
  refine Prod.ext (mul_zero a.1) (af_ext fun u => ?_)
  show evFin F u (a * idem v) = evFin F u 0
  rw [map_mul, map_zero]
  by_cases e : u = v
  · rw [e, h, zero_mul]
  · rw [ev_ne e, mul_zero]

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} : At (evFin F v) z ↔ idem v • z = z := by
  refine ⟨fun h => ?_, fun h u hu => by rw [← h, smul_smul, mul_idem hu, zero_smul]⟩
  have := h (1 - idem v) (by rw [map_sub, map_one, ev_self, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem idem_sq (v : Pl F) : idem v * idem v = idem v := by
  have := mul_idem (v := v) (a := 1 - idem v) (by rw [map_sub, map_one, ev_self, sub_self])
  linear_combination -this


variable (F) in
def Oh : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨(map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1).trans
    ((congrArg₂ (· + ·) ha.1 hb.1).trans (add_zero _)),
    fun v => by rw [map_add]; exact add_mem (ha.2 v) (hb.2 v)⟩
  neg_mem' := fun {a} ha => ⟨(map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1).trans
    ((congrArg Neg.neg ha.1).trans neg_zero), fun v => by rw [map_neg]; exact neg_mem (ha.2 v)⟩

theorem isCompact_Oh : IsCompact (Oh F : Set (AF F)) := by
  have h : IsCompact ((fun a : Af F => (show AF F from ((0, a) : Ainf F × Af F))) '' _) :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1.image (continuous_const.prodMk continuous_id)
  refine (Set.ext fun a => ?_ : _ = (Oh F : Set (AF F))) ▸ h
  refine ⟨?_, fun ha => ⟨a.2, ha.2, Prod.ext
    ((map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ha.1).symm rfl⟩⟩
  rintro ⟨b, hb, rfl⟩
  exact ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), hb⟩

theorem idem_mem {v : Pl F} {a : AF F} (h : evFin F v a ∈ v.adicCompletionIntegers F) : idem v * a ∈ Oh F := by
  refine ⟨?_, fun u => ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 * a.1) = 0
    rw [zero_mul, map_zero]
  · rw [map_mul]
    by_cases e : u = v
    · subst e; rwa [ev_self, one_mul]
    · rw [ev_ne e, zero_mul]; exact zero_mem _


variable (F) in
def incA : (Fin n → E) →+ (Fin n → AE F E) := AddMonoidHom.mk' (incV F) fun _ _ => funext fun _ => map_add _ _ _

variable {Y : Spc F E n}

omit [NumberField E] in
theorem gen_mem {a : AF F} (ha : a ∈ Oh F) {x : Fin n → E} (hx : x ∈ Y.L) : a • incV F x ∈ latHat Y :=
  AddSubgroup.subset_closure ⟨a, ha.1, ha.2, x, hx, rfl⟩

theorem lat_gen (hL : Y.L.IsLattice E) : ∃ (m : ℕ) (x : Fin m → Y.L), Submodule.span ℤ (Set.range x) = ⊤ ∧ ∀ z, z ∈ latHat Y ↔
    ∃ a : Fin m → AF F, (∀ i, a i ∈ Oh F) ∧ ∑ i, a i • incV F (x i).1 = z :=
  _root_.UpperTheory.Reformulated.B.OrthogonalGroupLemmas.lat_gen hL

theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact e.isEmbedding.t2Space

theorem isCompact_latHat (hL : Y.L.IsLattice E) : IsCompact (latHat Y : Set (Fin n → AE F E)) := by
  obtain ⟨m, x, -, hx⟩ := lat_gen hL
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have h := (isCompact_univ_pi fun _ : Fin m => isCompact_Oh (F := F)).image
    (f := fun a : Fin m → AF F => ∑ i, a i • incV F (x i).1)
    (by fun_prop)
  convert h using 1
  ext z
  exact (hx z).trans (exists_congr fun a => and_congr_left' (by simp))

theorem isClosed_latHat (hL : Y.L.IsLattice E) : IsClosed (latHat Y : Set (Fin n → AE F E)) :=
  have := t2Space_cm_host_adeles (F := F) (E := E)
  (isCompact_latHat hL).isClosed

def aeInt (Y : Spc F E n) : Submodule (AF F) (Fin n → AE F E) where
  carrier := {w | ∀ᶠ v : Pl F in cofinite, ∀ a ∈ Oh F, (idem v * a) • w ∈ latHat Y}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]
    exact Eventually.of_forall fun _ _ _ => by rw [smul_zero]; exact zero_mem _
  add_mem' := fun h h' => by
    rw [Set.mem_ofPred_eq] at *
    exact (h.and h').mono fun _ e a ha => by rw [smul_add]; exact add_mem (e.1 a ha) (e.2 a ha)
  smul_mem' := fun c w h => by
    rw [Set.mem_ofPred_eq] at *
    refine (h.and c.2.2).mono fun v e a ha => ?_
    have := e.1 _ (idem_mem (v := v) (a := a * c) (by rw [map_mul]; exact mul_mem (ha.2 v) e.2))
    rwa [← mul_assoc, idem_sq, ← mul_assoc, mul_smul] at this

omit [NumberField E] in
theorem aeInt_iff {w} : w ∈ aeInt Y ↔ ∀ᶠ v : Pl F in cofinite, ∀ a ∈ Oh F, (idem v * a) • w ∈ latHat Y := Iff.rfl

theorem mem_of_lat (hL : Y.L.IsFullLattice E) (P : Submodule (AF F) (Fin n → AE F E)) (hP : ∀ x ∈ Y.L, incV F x ∈ P)
    (w : Fin n → AE F E) : w ∈ P := by
  have h1 : ∀ x : Fin n → E, ∀ t : E, incV F (t • x) ∈ P := fun x => by
    induction (hL.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (Y.L : Set (Fin n → E))) using Submodule.span_induction with
    | mem x hx =>
      intro t
      obtain ⟨N, hN, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic t)).exists_integral_multiple
      have h2 : incV F ((N • t) • x) ∈ P := hP _ (Y.L.smul_mem (⟨N • t, hi⟩ : 𝓞 E) hx)
      have h3 := P.smul_mem (algebraMap F (AF F) (N : F)⁻¹) h2
      rwa [smul_assoc, show incV F (N • t • x) = N • incV F (t • x) from map_zsmul (incA F) _ _, ← Int.cast_smul_eq_zsmul (AF F),
        smul_smul, ← map_intCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hN), map_one, one_smul] at h3
    | zero => exact fun t => by rw [smul_zero, show incV F (0 : Fin n → E) = 0 from map_zero (incA F)]; exact zero_mem _
    | add x y _ _ hx hy =>
      intro t
      rw [smul_add, show incV F (t • x + t • y) = _ from map_add (incA F) _ _]
      exact add_mem (hx t) (hy t)
    | smul s x _ hx => exact fun t => by rw [smul_smul]; exact hx _
  rw [← Finset.univ_sum_single w]
  refine sum_mem fun i _ => ?_
  induction w i using TensorProduct.inductionOn with
  | add x y hx hy => rw [Pi.single_add]; exact add_mem hx hy
  | tmul a y =>
    convert P.smul_mem a (h1 (Pi.single i y) 1) using 1
    ext j
    by_cases e : j = i
    · subst e; simp [incV, inclR, TensorProduct.smul_tmul']
    · simp [incV, e]

theorem mem_aeInt (hL : Y.L.IsFullLattice E) (w : Fin n → AE F E) : w ∈ aeInt Y :=
  mem_of_lat hL _ (fun _ hx => aeInt_iff.2 <| Eventually.of_forall fun v _ ha => gen_mem (idem_mem (ha.2 v)) hx) w

theorem gen_surj (hL : Y.L.IsFullLattice E) {m : ℕ} {x : Fin m → Y.L} (hx : Submodule.span ℤ (Set.range x) = ⊤) :
    Function.Surjective (Fintype.linearCombination (AF F) fun i => incV F (x i).1) := fun w => by
  refine mem_of_lat hL (LinearMap.range _) (fun y hy => ?_) w
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hx ▸ Submodule.mem_top : (⟨y, hy⟩ : Y.L) ∈ _)
  have e := congrArg (fun t : Y.L => incA F t.1) hc

  simp only [AddSubmonoidClass.coe_finsetSum, map_sum, SetLike.val_smul_of_tower, map_zsmul] at e
  refine ⟨fun i => c i, Eq.trans ?_ e⟩
  rw [Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul _ _ _

theorem ae_mulVec (hL : Y.L.IsFullLattice E) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    ∀ᶠ v in cofinite, ∀ z ∈ latHat Y, At (evFin F v) z → A *ᵥ z ∈ latHat Y := by
  obtain ⟨m, x, -, hx⟩ := lat_gen hL.toIsLattice
  filter_upwards [eventually_all.2 fun i => aeInt_iff.1 (mem_aeInt hL (A *ᵥ incV F (x i).1))] with v hv z hz h
  obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
  rw [← at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
  exact sum_mem fun i _ => by rw [smul_smul, Matrix.mulVec_smul]; exact hv i _ (ha i)

end GlobalTheory.ThK.Dbl.Euler

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_conj {S R : Type} [CommRing S] [CommRing R] [Algebra S R] (c : R →ₐ[S] R) {n k : Type} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] (J : Matrix n n R) (P : Matrix n k R) (Q : Matrix k n R) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (D D' : Matrix k k R) (h3 : D * D' = 1) (h4 : D' * D = 1) (h : Dᵀ * (Pᵀ * J * P.map c) * D.map c = Pᵀ * J * P.map c) :
    ∃ g : UG c J, g.1.1 * P = P * D := by
  have mm : ∀ {a b e : Type} [Fintype b] (A : Matrix a b R) (B : Matrix b e R), (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := c.toRingHom)
  have u : ∀ A B : Matrix k k R, A * B = 1 → P * A * Q * (P * B * Q) = 1 := fun A B e => by
    rw [show P * A * Q * (P * B * Q) = P * (A * (Q * P) * B) * Q by simp only [Matrix.mul_assoc], h2, mul_one, e,
      Matrix.mul_one, h1]
  refine ⟨⟨⟨P * D * Q, P * D' * Q, u _ _ h3, u _ _ h4⟩, ?_⟩, by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  show (P * D * Q)ᵀ * J * (P * D * Q).map c = J
  calc _ = Qᵀ * (Dᵀ * (Pᵀ * J * P.map c) * D.map c) * Q.map c := by simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (P * Q)ᵀ * J * (P * Q).map c := by rw [h]; simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J := by rw [h1, Matrix.map_one _ (map_zero c) (map_one c)]; simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in
theorem incM_mul {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

omit [NumberField E] in
theorem incM_conj {a b : Type} (A : Matrix a b E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem leviEx : LeviEx := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H i₀ i₁ r s hB hW hH h₁
  have inv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  let N : Matrix (Fin d) (Fin 2) E := (Matrix.of ![H.x, H.y])ᵀ
  let P := Matrix.fromCols H.ι N
  have hsk (x y : Fin d → E) : form σ W.J x y = -σ (form σ W.J y x) := by

    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, inv, hW.skew, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hFull : W.L.IsFullLattice E := by
    let := hW.lat
    refine { span_eq_top := ?_ }
    let U := Submodule.span E (W.L : Set (Fin d → E))
    change U = ⊤
    by_contra hU
    let g : (Fin d → E) →ₗ[E] Module.Dual E U :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin W.Jᵀ)).domRestrict₂ U
    have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E (Fin d → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hU
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin d → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin d → E) (hx : x ∈ W.L) : form σ W.J y x = 0 := by
      have hz' : z ⬝ᵥ W.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E U => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have hzero : form σ W.J x y = 0 := by
        rw [Matrix.dotProduct_transpose_mulVec] at hz'
        simpa only [form, y, inv] using hz'
      rw [hsk, hzero, map_zero, neg_zero]
    have hline (a : E) : a • y ∈ W.L := by
      have hzform (x : Fin d → E) (hx : x ∈ W.L) : form σ W.J (a • y) x = 0 := by
        simpa only [form, smul_dotProduct, smul_eq_mul] using
          (show a * form σ W.J y x = 0 by rw [horth x hx, mul_zero])
      exact (hW.dual _).2 fun x hx o => by rw [hzform x hx, mul_zero, map_zero]; exact isIntegral_zero
    let i : E →ₗ[𝓞 E] W.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict W.L hline
    let : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have su : Function.Surjective P.mulVec := fun z => by
    letI := hFull
    have hz : z ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
      rw [Submodule.IsFullLattice.span_eq_top]
      exact Submodule.mem_top
    refine (Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun z hz => ?_) hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨Sum.elim u ![a, b], ?_⟩
    ext i
    simp [P, N, Matrix.mulVec, dotProduct]
    ring
  obtain ⟨Q, h1⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 su
  have h2 : Q * P = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [hH.rank]))).1 h1
  have o1 : H.ιᵀ * W.J * N.map σ = 0 := by
    ext i j
    have := hH.orth (Pi.single i 1)
    rw [Matrix.mul_assoc]
    fin_cases j
    · simpa [form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this.1
    · simpa [form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this.2
  have o2 : Nᵀ * W.J * H.ι.map σ = 0 := by
    ext j i
    have := congrArg σ (congrFun (congrFun o1 i) j)

    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, inv, hW.skew, Matrix.zero_apply,
    map_zero, Finset.sum_mul] at this ⊢
    rw [Finset.sum_comm, ← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have gr : Pᵀ * W.J * P.map σ = Matrix.fromBlocks W₁.J 0 0 (Nᵀ * W.J * N.map σ) := by
    rw [← hH.gram, ← o1]
    conv_rhs => enter [3]; rw [← o2]
    simp only [P]
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromCols_map, Matrix.fromRows_mul_fromCols]
  have one : ∀ {k : Type} [DecidableEq k], incM F (1 : Matrix k k E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have gr' : (incM F P)ᵀ * incM F W.J * (incM F P).map (cA σ) =
      Matrix.fromBlocks (incM F W₁.J) 0 0 (incM F (Nᵀ * W.J * N.map σ)) := by
    rw [incM_conj, show (incM F P)ᵀ = incM F Pᵀ from rfl, ← incM_mul, ← incM_mul, gr, incM, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    rfl
  obtain ⟨m, hm⟩ := exists_conj (cA σ) (incM F W.J) (incM F P) (incM F Q) (by rw [← incM_mul, h1, one])
    (by rw [← incM_mul, h2, one]) (Matrix.fromBlocks (mat h₁) 0 0 1) (Matrix.fromBlocks (h₁.1⁻¹).1 0 0 1)
    (by simp [Matrix.fromBlocks_multiply, mat]) (by simp [Matrix.fromBlocks_multiply, mat]) (by
      have e : (mat h₁)ᵀ * incM F W₁.J * (mat h₁).map (cA σ) = incM F W₁.J := h₁.2
      rw [gr', Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
      simp [Matrix.fromBlocks_multiply, e])
  rw [show incM F P = Matrix.fromCols (incM F H.ι) (incM F N) from Matrix.fromCols_map _ _ _, Matrix.mul_fromCols,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_ext_iff] at hm
  simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add] at hm
  refine ⟨m, ?_, ?_, hm.1⟩
  · rw [Units.val_one, one_smul]
    exact funext fun i => congrFun (congrFun hm.2 i) 0
  · rw [inv_one, Units.val_one, map_one, one_smul]
    exact funext fun i => congrFun (congrFun hm.2 i) 1

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def SplitModel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinW B.ψ t 1 1 ι) ∧ ∀ ι, M.IsLinW B.ψ t 1 1 ι →
      ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)),
        g₀.1 = (mat g).map (piW t) → h₀.1 = (mat h).map (piW t) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (g, h)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ)

def coef {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _)) (Φ : Fn F n d)
    (g : UA σ X.J) : ℂ := ∫ u, om (g, 1) Φ u * star (Φ u) ∂ν

def zint {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _))
    (a : G2 σ X → ℝ) (e : UA σ X.J × UA σ X.J →* G2 σ X) (Φ : Fn F n d) (s : ℂ) (g : UA σ X.J) : ℂ :=
  (a (e (g, 1)) : ℂ) ^ (s - ((d : ℂ) - n) / 2) * coef om ν Φ g


variable (σ Y) in
def locGrp (v : Pl F) : Subgroup (UA σ Y.J) := Subgroup.closure (UAt σ Y (evFin F v))

def IntAt (v : Pl F) (g : UA σ Y.J) : Prop :=
  ∀ z ∈ latHat Y, At (evFin F v) z → mat g *ᵥ z ∈ latHat Y ∧ mat g⁻¹ *ᵥ z ∈ latHat Y

def OffAt (v : Pl F) (g : UA σ Y.J) : Prop := (mat g).map (compFin F E v) = 1

def IsSphAt (K : Subgroup (G2 σ Y)) (χ : Chr F E) (v : Pl F) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t, IsPar p t → At (evFin F v) (mat2 p - 1) → ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
    f (p * k) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) * ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z


open Classical in
variable (E) in
def locD (n : ℕ) (v : Pl F) (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, (1 - (if Nonempty (E →ₐ[F] Fv F v) then 1 else -1) ^ (n - (i + 1)) *
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * s + (i + 1 : ℕ))))⁻¹

def NormZeta : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∃ (U : Set ℂ) (Z : ℂ → ℂ) (t₀ : ℝ),
      IsOpen U ∧ (∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) ∧ ((d : ℂ) - n) / 2 ∈ U ∧ DifferentiableOn ℂ Z U ∧
      (∀ z : ℂ, t₀ < z.re → z ∈ U ∧ Integrable (zint om ν a e Φ z) M.μ ∧ Z z = ∫ g, zint om ν a e Φ z g ∂M.μ) ∧
      (M.I om Φ = 0 → Z (((d : ℂ) - n) / 2) = 0)

def EulerProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (T : Finset (Pl F)) (μ : Measure (UA σ Y.J)),
    μ.IsHaarMeasure → ∀ (μl : ∀ v, Measure (locGrp σ Y v)), (∀ v, (μl v).IsHaarMeasure ∧ μl v {g | IntAt v g.1} = 1) →
    ∀ (f : UA σ Y.J → ℂ) (fl : Pl F → UA σ Y.J → ℂ), Integrable f μ →
      (∀ v ∉ T, (∀ u ∈ locGrp σ Y v, ∀ g, OffAt v g → f (u * g) = fl v u * f g) ∧ (∀ u ∈ locGrp σ Y v, IntAt v u → fl v u = 1) ∧
        Integrable (fun u : locGrp σ Y v => fl v u.1) (μl v)) →
      Tendsto (fun S : Finset {v : Pl F // v ∉ T} => (∏ v ∈ S, ∫ u, fl v.1 u.1 ∂μl v.1) * ∫ g in {g | ∀ v ∉ T, IntAt v g}, f g ∂μ)
        atTop (𝓝 (∫ g, f g ∂μ))

def LocMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ v,
    ∃ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure ∧ μ {g | IntAt v g.1} = 1

def LocUnr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

def BadFactor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → n ≤ d → Even d → ∀ T : Finset (Pl F), T ⊆ B.P → UnrOff χX (T : Set (Pl F)) →
    UnrOff χW (T : Set (Pl F)) → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → (∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀) →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ Φ ∈ PolData B M,
      (∀ (z : ℂ), ∀ v ∉ T, ∃ f, IsSphAt K χW v (z + n / 2) f ∧ ∀ u ∈ locGrp σ X v, (IntAt v u → f (e (u, 1)) = 1) ∧
        ∀ g, OffAt v g → zint om ν a e Φ z (u * g) = f (e (u, 1)) * zint om ν a e Φ z g) ∧
      Differentiable ℂ (fun z => ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ) ∧
      ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ (((d : ℂ) - n) / 2) g ∂M.μ ≠ 0

def RealInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] [Nontrivial P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P),
    RealQuot B M om p → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀

def DProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (T : Finset (Pl F)), ∃ d : ℂ → ℂ,
    DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re → d z ≠ 0 ∧
      HasProd (fun v : {v : Pl F // v ∉ T} => locD E n v.1 z) (d z)

end GlobalTheory.ThK.Dbl

end
end
