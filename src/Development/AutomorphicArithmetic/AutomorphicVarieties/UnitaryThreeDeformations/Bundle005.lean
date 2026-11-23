module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle002
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

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ} {I M : Ideal C}

private theorem entIn_mul_left (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem entIn_thetaLie {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (thetaLie X) := fun a b => by
  have h : EntIn I Xᵀ := fun a b => hX b a
  exact I.neg_mem (entIn_mul_right _ (entIn_mul_left _ h) a b)

private theorem entIn_ite (s : ℤˣ) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (if s = 1 then X else thetaLie X) := by
  split_ifs
  · exact hX
  · exact entIn_thetaLie hX

private theorem entIn_adFun (x : GG (m := m) (R := C)) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (x.adFun X) :=
  entIn_mul_right _ (entIn_mul_left _ (entIn_ite _ hX))

private theorem entIn_mul_zero (hI : M * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C}
    (hX : EntIn M X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := Ideal.mul_mem_mul (hX a k) (hY k b)
  rwa [hI, Ideal.mem_bot] at this

private theorem adFun_congr (hI : M * I = ⊥) {x y : GG (m := m) (R := C)} (hr : x.right = y.right)
    (hm : EntIn M (x.mat - y.mat)) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    x.adFun X = y.adFun X := by
  unfold GG.adFun
  rw [hr]
  have hY := entIn_ite y.right hX
  generalize (if y.right = 1 then X else thetaLie X) = Y at hY ⊢
  have h1 : x.mat * Y = y.mat * Y := by
    rw [← sub_eq_zero, ← Matrix.sub_mul]
    exact entIn_mul_zero hI hm hY
  have h2 : ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) -
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (x.mat - y.mat) *
        ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
    simp only [GG.mat, Matrix.mul_sub, Matrix.sub_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [h1, eq_comm, ← sub_eq_zero, ← Matrix.mul_sub, h2]
  exact entIn_mul_zero (by rwa [mul_comm]) (entIn_mul_left _ hY)
    (entIn_mul_right _ (entIn_mul_left _ hm))

private def onePlus (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) : GL (Fin m) C where
  val := 1 + X
  inv := 1 - X
  val_inv := by simp [Matrix.add_mul, Matrix.mul_sub, h]
  inv_val := by simp [Matrix.mul_add, Matrix.sub_mul, h]

private theorem sgnAct_one_add (hI : I * I = ⊥) (q : GL (Fin m) C)
    (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) (hq : (q : Matrix (Fin m) (Fin m) C) = 1 + X)
    (s : ℤˣ) :
    ((sgnAct m C s q : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp [hq]
  · have hinv : ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hq, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, entIn_mul_zero hI hX hX]
      simp
    rw [sgnAct_neg_one, theta_val, hinv]
    simp only [h, if_false, thetaLie, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat]
    rw [sub_eq_add_neg]

private structure Near (I : Ideal C) (y : GG (m := m) (R := C)) (X : Matrix (Fin m) (Fin m) C) : Prop where
  right : y.right = 1
  mat : y.mat = 1 + X
  ent : EntIn I X

private theorem act_act (s : ℤˣ) (g : GL (Fin m) C) : sgnAct m C s (sgnAct m C s g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]

private theorem Near.mul_mat {y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C} (h : Near I y X) (x : GG (m := m) (R := C)) :
    (y * x).mat = (1 + X) * x.mat := by
  rw [← h.mat]
  simp [GG.mat, h.right]

private theorem Near.mul (hI : I * I = ⊥) {y y' : GG (m := m) (R := C)} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X') : Near I (y * y') (X + X') := by
  refine ⟨by simp [h.right, h'.right], ?_, fun a b => I.add_mem (h.ent a b) (h'.ent a b)⟩
  rw [h.mul_mat, h'.mat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, entIn_mul_zero hI h.ent h'.ent,
    Matrix.mul_one]
  abel

private theorem Near.conj (hI : I * I = ⊥) {y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (x : GG (m := m) (R := C)) : Near I (x * y * x⁻¹) (x.adFun X) := by
  refine ⟨by simp [h.right], ?_, entIn_adFun x h.ent⟩
  have e : (x * y * x⁻¹).left = x.left * sgnAct m C x.right y.left * x.left⁻¹ := by
    simp [h.right, act_act]
  rw [GG.mat, e, Units.val_mul, Units.val_mul, sgnAct_one_add hI _ _ h.ent h.mat, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Units.mul_inv]
  rfl

private theorem Near.uniq {y : GG (m := m) (R := C)} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y X') : X = X' :=
  add_left_cancel (h.mat.symm.trans h'.mat)

private theorem Near.eq {y y' : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X) : y = y' := by
  ext1
  · exact Units.ext (h.mat.trans h'.mat.symm)
  · rw [h.right, h'.right]

private theorem exists_near (hI : I * I = ⊥) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    ∃ y : GG (m := m) (R := C), Near I y X :=
  ⟨⟨onePlus X (entIn_mul_zero hI hX hX), 1⟩, rfl, rfl, hX⟩

private theorem near_of {x y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X)
    (hr : x.right = y.right) (hm : x.mat = (1 + X) * y.mat) : Near I (x * y⁻¹) X := by
  refine ⟨by simp [hr], ?_, hX⟩
  have e : (x * y⁻¹).left = x.left * y.left⁻¹ := by simp [hr, act_act]
  rw [GG.mat, e, Units.val_mul]
  change x.mat * _ = _
  rw [hm, GG.mat, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.lt_corr :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → K ≤ maximalIdeal R → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ s : D → GG (m := 3) (R := R), IsLocallyConstant s → (∀ g, (s g).right = η g) →
      (∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ g).mat).map (algebraMap O R))) →
      (∀ g h, ∃ c ∈ gw R j, EntIn K c ∧ (s g * s h).mat = (1 + c) * (s (g * h)).mat) →
      ∃ r : D →* GG (m := 3) (R := R), IsLocallyConstant (mats r) ∧ ∀ g, (r g).right = η g ∧ ∃ b ∈ gw R j, EntIn K b ∧ (r g).mat = (1 + b) * (s g).mat := by
  intro O R D _ _ _ _ _ _ _ _ _ η Ψ K j hK hle hH s hs hη hred hc
  have hKK : K * K = ⊥ := le_bot_iff.1 (hK ▸ Ideal.mul_mono_left hle)
  choose c hcw hcK hcm using hc
  have hu : ∀ g h, Near K (s g * s h * (s (g * h))⁻¹) (c g h) := fun g h =>
    near_of (hcK g h) (by simp [hη]) (hcm g h)
  have had : ∀ g {X : Matrix (Fin 3) (Fin 3) R}, EntIn K X →
      (s g).adFun X = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g X := fun g X hX =>
    adFun_congr hK (y := GG.map (algebraMap O R) (r0 η Ψ g)) (hη g) (hred g) hX
  have hlc : IsLocallyConstant fun z : D × D => c z.1 z.2 := by
    have e : (fun z : D × D => c z.1 z.2) =
        (fun w : (GG (m := 3) (R := R) × GG (m := 3) (R := R)) × GG (m := 3) (R := R) => (w.1.1 * w.1.2 * w.2⁻¹).mat - 1) ∘
          fun z : D × D => ((s z.1, s z.2), s (z.1 * z.2)) := by
      funext z
      simp only [Function.comp_apply, (hu z.1 z.2).mat, add_sub_cancel_left]
    rw [e]
    exact (((hs.comp_continuous continuous_fst).prodMk (hs.comp_continuous continuous_snd)).prodMk
      (hs.comp_continuous continuous_mul)).comp _
  obtain ⟨b, hb, hbw, hbK, hbe⟩ := lifting_obstruction_second_cohomology η Ψ K j hK hH (fun z => c z.1 z.2) hlc (fun z => hcw _ _)
    (fun z => hcK _ _) (fun g h k => by
      have h1 := (hu g h).mul hKK (hu (g * h) k)
      have h2 := ((hu h k).conj hKK (s g)).mul hKK (hu g (h * k))
      have e : s g * s h * (s (g * h))⁻¹ * (s (g * h) * s k * (s (g * h * k))⁻¹) =
          s g * (s h * s k * (s (h * k))⁻¹) * (s g)⁻¹ * (s g * s (h * k) * (s (g * (h * k)))⁻¹) := by
        rw [mul_assoc g h k]; group
      rw [e] at h1
      have h3 := h1.uniq h2
      rw [had g (hcK h k)] at h3
      dsimp only
      rw [sub_add_eq_add_sub, ← h3]
      abel)
  have hnb : ∀ g, EntIn K (-b g) := fun g a a' => K.neg_mem (hbK g a a')
  choose e he using fun g => exists_near hKK (hnb g)
  have hmul : ∀ g h, e (g * h) * s (g * h) = e g * s g * (e h * s h) := fun g h => by
    have h1 := ((he g).mul hKK ((he h).conj hKK (s g))).mul hKK (hu g h)
    have h2 : -b g + (s g).adFun (-b h) + c g h = -b (g * h) := by
      have := hbe g h
      dsimp only at this
      rw [had g (hnb h), map_neg, this]
      abel
    rw [h2] at h1
    rw [← h1.eq (he (g * h))]
    group
  refine ⟨MonoidHom.mk' (fun g => e g * s g) hmul, ?_, fun g => ⟨?_, -b g, neg_mem (hbw g), hnb g,
    (he g).mul_mat _⟩⟩
  · have e' : mats (MonoidHom.mk' (fun g => e g * s g) hmul) =
        (fun w : Matrix (Fin 3) (Fin 3) R × GG (m := 3) (R := R) => (1 + -w.1) * w.2.mat) ∘ fun g => (b g, s g) := by
      funext g
      exact (he g).mul_mat _
    rw [e']
    exact (hb.prodMk hs).comp _
  · show (e g * s g).right = η g
    simp [(he g).right, hη]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul' {O σ : Type} [CommRing O] (i : σ) (f g : MvPowerSeries σ O) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + constantCoeff g * coeff (Finsupp.single i 1) f := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ]
  ring

private noncomputable def lin {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] : (σ → Q) →+ (FA O wt →ₗ[O] Q) where
  toFun v :=
    { toFun := fun f => ∑ i, coeff (Finsupp.single i 1) (ser f) • v i
      map_add' := fun f g => by
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a f => by
        simp [Finset.smul_sum, mul_smul] }
  map_zero' := by ext f; simp
  map_add' v w := by ext f; simp [Finset.sum_add_distrib]

private theorem lin_apply {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (f : FA O wt) :
    lin wt Q v f = ∑ i, coeff (Finsupp.single i 1) (ser f) • v i := rfl

private theorem lin_zA {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (i : σ) :
    lin wt Q v ((WPres.free O wt).zA i) = v i := by
  classical
  rw [lin_apply]
  have : ser ((WPres.free O wt).zA i) = (X i : MvPowerSeries σ O) := rfl
  rw [this, Finset.sum_eq_single i]
  · simp [coeff_X]
  · intro b _ hb
    rw [coeff_X, if_neg, zero_smul]
    intro h
    exact hb (Finsupp.single_left_injective one_ne_zero h)
  · simp

theorem UpperTheory.length_le_cotLen_of_injective_tangent_map :
    LemmaM' → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] (σ : Type) [Fintype σ] (wt : σ → ℤ) (j : ℤ), j ≠ 0 →
        ∀ (κ : Type) (F : κ → FA O wt), (∀ k, F k ∈ Fgr O wt j) → ∀ c : O, c ≠ 0 →
        ∀ (M : Type) [AddCommGroup M] [Module O M] (d : M →+ (σ → O ⧸ Ideal.span {c})), Function.Injective d →
        (∀ μ i, wt i ≠ j → d μ i = 0) → (∀ μ k, ∑ i, coeff (Finsupp.single i 1) (ser (F k)) • d μ i = 0) →
        Module.length O M ≤ cotLen (x0 O wt) (Fgr O wt) j F := by
  intro hM O _ _ _ _ σ _ wt j hj κ F hF c hc M _ _ d hd hwt hker
  classical
  let D : M →+ (FA O wt →ₗ[O] O ⧸ Ideal.span {c}) := (lin wt (O ⧸ Ideal.span {c})).comp d
  have hD : ∀ μ f, D μ f = ∑ i, coeff (Finsupp.single i 1) (ser f) • d μ i :=
    fun μ f => lin_apply wt _ (d μ) f
  have hwsingle : ∀ i : σ, (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
    intro i
    simp [Finsupp.weight_apply]
  refine hM O (FA O wt) ℤ (Fgr O wt) (x0 O wt) j ?_ κ F hF c hc M D ?_ ?_ ?_
  · intro f hf
    rw [weightedSeriesOrigin_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact (mem_Fgr.mp hf) 0 (by simpa using hj.symm)
  · intro μ ν h
    apply hd
    funext i
    have h2 := congrArg (fun L : FA O wt →ₗ[O] O ⧸ Ideal.span {c} => L ((WPres.free O wt).zA i))
      (congrArg (fun T => T) h)
    simpa [D, lin_zA] using h2
  · intro μ k
    rw [hD]
    exact hker μ k
  · intro μ
    choose e he using fun i => Ideal.Quotient.mk_surjective (d μ i)
    let e' : σ → O := fun i => if wt i = j then e i else 0
    have he' : ∀ i, Ideal.Quotient.mk (Ideal.span {c}) (e' i) = d μ i := by
      intro i
      by_cases h : wt i = j
      · simp [e', h, he]
      · simp [e', h, hwt μ i h]
    refine ⟨lin wt O e', ?_, ?_, ?_⟩
    · intro f g
      have hs : ser (f * g) = ser f * ser g := rfl
      rw [lin_apply, lin_apply, lin_apply, weightedSeriesOrigin_apply, weightedSeriesOrigin_apply, hs]
      simp only [coeff_single_mul', smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · intro i' hi' f hf
      rw [lin_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : wt i = j
      · have h0 : coeff (Finsupp.single i 1) (ser f) = 0 := by
          refine (mem_Fgr.mp hf) _ ?_
          rw [hwsingle, h]
          exact fun e => hi' e.symm
        rw [h0, zero_smul]
      · simp [e', h]
    · intro f

      rw [hD, lin_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← he' i, smul_eq_mul, map_mul, Algebra.smul_def]
      rfl
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul {O σ : Type} [CommRing O] (i : σ) (a g : MvPowerSeries σ O)
    (hg : constantCoeff g = 0) :
    coeff (Finsupp.single i 1) (a * g) = constantCoeff a * coeff (Finsupp.single i 1) g := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, hg]

private noncomputable def pad {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n) : FA O wt :=
  if h : k.val < b then mkF (f ⟨k.val, h⟩) (hf _) else 0

private theorem pad_ind {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n)
    (P : FA O wt → Prop) (h0 : P 0) (h1 : ∀ i, P (mkF (f i) (hf i))) : P (pad f hf n k) := by
  unfold pad
  split_ifs
  · exact h1 _
  · exact h0

private theorem pad_range {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) {n : ℕ} (h : b ≤ n) (i : Fin b) :
    mkF (f i) (hf i) ∈ Set.range (pad f hf n) :=
  ⟨⟨i.val, lt_of_lt_of_le i.2 h⟩, by simp [pad]⟩

private theorem der_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (ho : W.HasOrigin)
    (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O) (hf : ∀ j i, f j i ∈ wtPart O W.wt j)
    (hk : RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j))) (j0 : ℤ) (n : ℕ) (hn : b j0 ≤ n)
    (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N) (hd : ∀ i, W.wt i ≠ j0 → d i = 0)
    (hF : ∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (pad (f j0) (hf j0) n k)) • d i = 0)
    (g : MvPowerSeries W.σ O) (hg : W.π g = 0) : ∑ i, coeff (Finsupp.single i 1) g • d i = 0 := by
  have hg' : g ∈ Ideal.span (⋃ j, Set.range (f j)) := hk ▸ hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hx
    by_cases hj : j = j0
    · subst hj
      obtain ⟨k, e⟩ := pad_range (f j) (hf j) hn i
      have := hF k
      rwa [e] at this
    · refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : W.wt v = j0
      · rw [hf j i _ (by simpa [Finsupp.weight_single, hv] using Ne.symm hj), zero_smul]
      · rw [hd v hv, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul a x hx ih =>
    have h0 : constantCoeff x = 0 := ho x (hk.ge hx)
    simp only [smul_eq_mul, coeff_single_mul _ a x h0, mul_smul, ← Finset.smul_sum, ih, smul_zero]

theorem UpperTheory.exists_weighted_equations_presenting_ker :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R), W.HasOrigin →
        ∀ (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O), (∀ j i, f j i ∈ wtPart O W.wt j) →
        RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j)) → ∀ r s r' s' m : ℕ,
        b (-1) ≤ r + 1 → b (-2) ≤ s → b 1 ≤ r' → b 2 ≤ s' → b 0 ≤ m → (∀ j, j < -2 ∨ 2 < j → b j = 0) →
        ∃ Q : Eqns (Fgr O W.wt) (x0 O W.wt) r s r' s' m, Q.ideal = RingHom.ker (toA W) ∧
          ∀ (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N),
            (((∀ i, W.wt i ≠ -1 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.F k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ -2 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.G k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ 0 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.Z k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0)) := by
  intro O R _ _ _ W ho b f hf hk r s r' s' m h1 h2 h3 h4 h5 h6
  have hker : ∀ j i, W.π (f j i) = 0 := fun j i => by
    have : f j i ∈ RingHom.ker W.π := hk ▸ Ideal.subset_span (Set.mem_iUnion.2 ⟨j, i, rfl⟩)
    exact this
  have hmem : ∀ j n k, pad (f j) (hf j) n k ∈ Fgr O W.wt j := fun j n k =>
    pad_ind _ _ n k (· ∈ Fgr O W.wt j) (zero_mem _) fun i => mkF_mem _ _
  have hkA : ∀ j n, Set.range (pad (f j) (hf j) n) ⊆ RingHom.ker (toA W) := by
    rintro j n _ ⟨k, rfl⟩
    exact pad_ind _ _ n k (· ∈ RingHom.ker (toA W)) (zero_mem _) fun i => Subtype.ext (hker j i)
  refine ⟨⟨pad (f (-1)) (hf _) _, pad (f (-2)) (hf _) _, pad (f 1) (hf _) _, pad (f 2) (hf _) _,
    pad (f 0) (hf _) _, hmem _ _, hmem _ _, hmem _ _, hmem _ _, fun k => ⟨hmem _ _ _, ?_⟩⟩, ?_,
    fun N _ _ d => ⟨der_zero W ho b f hf hk _ _ h1 N d, der_zero W ho b f hf hk _ _ h2 N d,
      der_zero W ho b f hf hk _ _ h5 N d⟩⟩
  · exact pad_ind _ _ m k (fun y => x0 O W.wt y = 0) (map_zero _) fun i => by
      rw [weightedSeriesOrigin_apply]; exact ho _ (hker 0 i)
  · refine le_antisymm (Ideal.span_le.2 ?_) fun x hx => ?_
    · simp only [Set.union_subset_iff]
      exact ⟨⟨⟨⟨hkA _ _, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩
    · have hx1 : ser x ∈ RingHom.ker W.π := congrArg Subtype.val (show toA W x = 0 from hx)
      rw [hk] at hx1
      have H := (homog_span O _ ℤ (WPres.free O W.wt) (Σ j : Finset.Icc (-2 : ℤ) 2, Fin (b j))
        (fun p => mkF (f p.1 p.2) (hf _ _)) (fun p => p.1) (fun p => mkF_mem _ _)).2 x
      refine Ideal.span_mono ?_ (H.1 (Ideal.span_mono ?_ hx1))
      · rintro _ ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
        have hj' := Finset.mem_Icc.1 hj
        have : j = -1 ∨ j = -2 ∨ j = 1 ∨ j = 2 ∨ j = 0 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inl (pad_range _ _ h1 i))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr (pad_range _ _ h2 i))))
        · exact Or.inl (Or.inl (Or.inr (pad_range _ _ h3 i)))
        · exact Or.inl (Or.inr (pad_range _ _ h4 i))
        · exact Or.inr (pad_range _ _ h5 i)
      · intro y hy
        obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hy
        have hj : j ∈ Finset.Icc (-2 : ℤ) 2 := by
          by_contra hc
          have := h6 j (by rw [Finset.mem_Icc] at hc; omega)
          have := i.2
          omega
        exact ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
end
