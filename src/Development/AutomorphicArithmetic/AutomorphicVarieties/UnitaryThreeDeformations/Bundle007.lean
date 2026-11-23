module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
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

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem gg_ext {R : Type} [CommRing R] {x y : GG (m := 3) (R := R)} (h1 : x.right = y.right) (h2 : x.mat = y.mat) :
    x = y := SemidirectProduct.ext (Units.ext h2) h1

private theorem exists_weight_inv_det_left_mem_weight_piece {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] (u : Γ →* GG (m := 3) (R := R)) (g : Γ) : ∃ j : ℤ, (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ wpart (O := O) u j := by
  have hth : ∀ {R' : Type} [CommRing R'] (k : GL (Fin 3) R'), GeneralLinearGroup.det (thetaAut 3 R' k) = (GeneralLinearGroup.det k)⁻¹ := by
    intro R' _ k
    have hJ : GeneralLinearGroup.det (Jgl (R := R') 3) * GeneralLinearGroup.det (Jgl (R := R') 3) = 1 := by
      rw [← map_mul, Jgl_mul_Jgl, map_one]
    have hT : GeneralLinearGroup.det (trInv k) = (GeneralLinearGroup.det k)⁻¹ := by
      rw [← map_inv]
      apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, trInv, Matrix.det_transpose]
    show GeneralLinearGroup.det (theta k) = _
    simp only [theta, map_mul, hT]
    rw [mul_right_comm, hJ, one_mul]
  have htor : ∀ {R' : Type} [CommRing R'] (t : R'ˣ), GeneralLinearGroup.det (tor R' t) = t ^ (wt1 0 + wt1 1 + wt1 2) := by
    intro R' _ t
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, tor, torGL, Matrix.det_diagonal, Fin.prod_univ_three, _root_.zpow_add]
  refine ⟨if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2)), ?_⟩
  intro R' _ _ _ f f' t h
  have hg := congrArg (fun φ => GeneralLinearGroup.det (φ g).left) h
  simp only [_root_.UpperTheory.V.UnitaryThreeInertia.push, conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, GG.ofGL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, GG.map, SemidirectProduct.map_left, map_mul, GeneralLinearGroup.map_det] at hg
  simp only [map_one, inv_one, MulAut.one_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.map_right, MonoidHom.id_apply, one_mul, map_inv, htor] at hg
  have key : (Units.map (f' : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ = t ^ (if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2))) * (Units.map (f : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ := by
    rw [map_inv, map_inv]
    split_ifs with hs
    · rw [hs, map_one, MulAut.one_apply, GeneralLinearGroup.map_det, htor] at hg
      rw [hg, mul_right_comm, mul_inv_cancel, one_mul, zpow_zero, one_mul]
    · have : sgnAct 3 R' (u g).right = thetaAut 3 R' := by simp [sgnAct, hs]
      rw [this, hth, inv_inv, htor, GeneralLinearGroup.map_det] at hg
      rw [hg]
      generalize wt1 0 + wt1 1 + wt1 2 = w
      rw [show -(2 * w) = -w + -w by ring, _root_.zpow_add, _root_.zpow_neg]
      simp only [_root_.mul_inv_rev]
      ac_rfl
  have e : ∀ φ : R →ₐ[O] R', φ (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) = ((Units.map (φ : R →+* R') (GeneralLinearGroup.det (u g).left)⁻¹ : R'ˣ) : R') := fun φ => rfl
  rw [e f', e f, key, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.existsUnique_isPtHom :
    ∀ {O R Γ K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] [CommRing K] [Algebra O K] (u : Γ →* GG (m := 3) (R := R)) (ξ : Sring (O := O) u →ₐ[O] K), ∃! r, IsPtHom u ξ r := by
  intro O R Γ K _ _ _ _ _ _ _ u ξ
  have hmem : ∀ g a b, (u g).mat a b ∈ Sring (O := O) u := fun g a b =>
    mem_Sring u (entry_mem u g a b)
  have hinv : ∀ g a b, (((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b ∈ Sring (O := O) u := by
    intro g a b
    obtain ⟨j, hj⟩ := exists_weight_inv_det_left_mem_weight_piece (O := O) u g
    have hd : (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ Sring (O := O) u :=
      mem_Sring u hj
    let M' : Matrix (Fin 3) (Fin 3) (Sring (O := O) u) := fun a b => ⟨(u g).mat a b, hmem g a b⟩
    have hM : ((Sring (O := O) u).val : Sring (O := O) u →+* R).mapMatrix M' = ((u g).left : Matrix (Fin 3) (Fin 3) R) := by
      ext a b; rfl
    have hdet : ((u g).left : Matrix (Fin 3) (Fin 3) R).det = ((GeneralLinearGroup.det (u g).left : Rˣ) : R) :=
      (GeneralLinearGroup.val_det_apply _).symm
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_unit, ← hM, ← RingHom.map_adjugate]
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (Sring (O := O) u).mul_mem hd (M'.adjugate a b).2
  have hinj : Function.Injective (((Sring (O := O) u).val : Sring (O := O) u →+* R).mapMatrix (m := Fin 3)) := by
    intro x y h
    ext a b
    exact congrFun (congrFun h a) b
  let large₂ : Γ → GL (Fin 3) (Sring (O := O) u) := fun g =>
    { val := Matrix.of fun a b => ⟨(u g).mat a b, hmem g a b⟩
      inv := Matrix.of fun a b => ⟨(((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b, hinv g a b⟩
      val_inv := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.val_inv using 2 <;> ext a b <;> rfl
      inv_val := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.inv_val using 2 <;> ext a b <;> rfl }
  have gmap_inj : Function.Injective (GG.map (m := 3) ((Sring (O := O) u).val : Sring (O := O) u →+* R)) := by
    intro x y h
    apply gg_ext
    · have := congrArg (fun z => z.right) h
      simpa [GG.map_right] using this
    · ext a b
      have := congrArg (fun z => z.mat a b) h
      simpa [GG.map_mat] using this
  let vf : Γ → GG (m := 3) (R := Sring (O := O) u) := fun g => SemidirectProduct.mk (large₂ g) (u g).right
  have hv : ∀ g, GG.map ((Sring (O := O) u).val : Sring (O := O) u →+* R) (vf g) = u g := by
    intro g
    apply gg_ext
    · rw [GG.map_right]
    · ext a b
      rw [GG.map_mat]
      rfl
  let v : Γ →* GG (m := 3) (R := Sring (O := O) u) :=
    { toFun := vf
      map_one' := gmap_inj (by rw [hv, map_one, map_one])
      map_mul' := fun x y => gmap_inj (by rw [map_mul, hv, hv, hv, map_mul]) }
  have h0 : IsPtHom u ξ ((GG.map (ξ : Sring (O := O) u →+* K)).comp v) := by
    intro g
    constructor
    · show (GG.map _ (vf g)).right = _
      rw [GG.map_right]
    · show (GG.map _ (vf g)).mat = _
      rw [GG.map_mat]
      ext a b
      rfl
  refine ⟨_, h0, fun r hr => MonoidHom.ext fun g => gg_ext ((hr g).1.trans (h0 g).1.symm) ((hr g).2.trans (h0 g).2.symm)⟩
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem canon_eig {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (h : GL (Fin 3) R) (hc : Canon X h) :
    ∃ d : Fin 3 → R, ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal d ∧
      ∀ a, d a - X a a ∈ maximalIdeal R := by
  let φ := residue R
  have h0 : φ.mapMatrix (h.val - 1) = 0 := by
    ext a b
    exact (residue_eq_zero_iff _).2 (hc.hat a b)
  have hh : φ.mapMatrix h.val = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0
  have hhi : φ.mapMatrix h⁻¹.val = 1 := by
    have e : φ.mapMatrix h⁻¹.val * φ.mapMatrix h.val = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rwa [hh, mul_one] at e
  refine ⟨fun a => (h⁻¹.val * X * h.val) a a, hc.diag.diagonal_diag.symm, ?_⟩
  intro a
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  have e : φ.mapMatrix (h⁻¹.val * X * h.val) = φ.mapMatrix X := by
    rw [map_mul, map_mul, hh, hhi, one_mul, mul_one]
  exact congrFun (congrFun e a) a

theorem UpperTheory.V.UnitaryThreeInertia.canon_unique :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h h' : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → Canon X h → Canon X h' → h = h' := by
  intro R _ _ X h h' hX hc hc'
  obtain ⟨d, hd, hdX⟩ := canon_eig X h hc
  obtain ⟨d', hd', hd'X⟩ := canon_eig X h' hc'
  let g : GL (Fin 3) R := h⁻¹ * h'
  have key : diagonal d * g.val = g.val * diagonal d' := by
    rw [← hd, ← hd']
    simp only [g, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  have hg : ∀ a b, a ≠ b → g.val a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun key a) b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hu : IsUnit (d a - d' b) := by
      by_contra hn
      have hm : d a - d' b ∈ maximalIdeal R := hn
      have hm2 : X a a - X b b ∈ maximalIdeal R := by
        have e2 : X a a - X b b = (d a - d' b) - (d a - X a a) + (d' b - X b b) := by ring
        rw [e2]
        exact add_mem (sub_mem hm (hdX a)) (hd'X b)
      exact hm2 (hX a b hab)
    have e3 : g.val a b * (d a - d' b) = 0 := by
      rw [mul_sub, mul_comm (g.val a b) (d a), e, sub_self]
    exact hu.mul_left_eq_zero.1 e3
  have hh' : h'.val = h.val * g.val := by
    simp only [g, Units.val_mul, Units.mul_inv_cancel_left]
  have g1 : g.val = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have e := congrFun (congrFun hh' a) a
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hg c a hc, mul_zero])
        (by simp), hc'.one a, hc.one a, one_mul] at e
      exact e.symm
    · rw [Matrix.one_apply_ne hab, hg a b hab]
  have g1' : g = 1 := Units.ext g1
  exact inv_mul_eq_one.1 g1'
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem tor_conj_apply {R : Type} [CommRing R] (t : Rˣ) (Y : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    ((tor R t).val * Y * (tor R t⁻¹).val) a b =
      ((t ^ wt1 a : Rˣ) : R) * Y a b * ((t⁻¹ ^ wt1 b : Rˣ) : R) := by
  rw [tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem tor_mul_inv {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t⁻¹).val * (tor R t).val = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

private theorem tor_mul_inv' {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t).val * (tor R t⁻¹).val = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem UpperTheory.V.UnitaryThreeInertia.canon_map :
    (∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), Canon X h → Canon (X.map φ) (GeneralLinearGroup.map φ h)) ∧
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R) (t : Rˣ), Canon X h → Canon ((tor R t).val * X * (tor R t⁻¹).val) (tor R t * h * tor R t⁻¹) := by
  refine ⟨fun {R R'} _ _ _ _ φ _ X h H => ⟨fun a b => ?_, fun a => ?_, ?_⟩,
    fun {R} _ _ X h t H => ⟨fun a b => ?_, fun a => ?_, ?_⟩⟩
  · have e : ((GeneralLinearGroup.map φ h : GL (Fin 3) R').val - 1) a b = φ ((h.val - 1) a b) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]; rfl
      · rw [map_zero]; rfl
    rw [e]
    exact map_nonunit φ _ (H.hat a b)
  · show φ (h.val a a) = 1
    rw [H.one, map_one]
  · have e : ((GeneralLinearGroup.map φ h)⁻¹ : GL (Fin 3) R').val * X.map φ * (GeneralLinearGroup.map φ h).val =
        ((h⁻¹ : GL (Fin 3) R).val * X * h.val).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, ← map_inv]; rfl
    rw [e]
    exact H.diag.map (map_zero φ)
  · have e : (tor R t * h * tor R t⁻¹).val - 1 = (tor R t).val * (h.val - 1) * (tor R t⁻¹).val := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, tor_mul_inv', Units.val_mul, Units.val_mul]
    rw [e, tor_conj_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (H.hat a b))
  · rw [Units.val_mul, Units.val_mul, tor_conj_apply, H.one, mul_one, ← Units.val_mul, ← mul_zpow,
      mul_inv_cancel, _root_.one_zpow, Units.val_one]
  · have e : ((tor R t * h * tor R t⁻¹)⁻¹ : GL (Fin 3) R).val * ((tor R t).val * X * (tor R t⁻¹).val) *
        (tor R t * h * tor R t⁻¹).val = (tor R t).val * ((h⁻¹ : GL (Fin 3) R).val * X * h.val) * (tor R t⁻¹).val := by
      have hc : ∀ Y : Matrix (Fin 3) (Fin 3) R, (tor R t⁻¹).val * ((tor R t).val * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, tor_mul_inv, Matrix.one_mul]
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, inv_inv]
      simp only [Units.val_mul, Matrix.mul_assoc, hc]
    rw [e]
    intro a b hab
    rw [tor_conj_apply, H.diag hab, mul_zero, zero_mul]
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  rfl

private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, _root_.UpperTheory.V.UnitaryThreeInertia.push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply,
    map_mul, map_ofGL]

private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R))
    (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]; rfl

private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I (_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨htri, hine⟩ := H
  refine ⟨?_, ?_⟩
  · unfold Upper at htri ⊢
    intro g hg a b hab
    rw [conj_push_mat, htri g hg a b hab, map_zero]
  · intro s hs hη a
    rw [conj_push_mat, hine s hs hη a, AlgHom.commutes]

private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I (_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨H1, hlow⟩ := H
  refine ⟨triIn_push φ H1, ?_⟩
  unfold Lower at hlow ⊢
  intro g hg a b hab
  rw [conj_push_mat, hlow g hg a b hab, map_zero]

variable [IsLocalRing R] [IsLocalRing R']

private theorem map_mem_max (φ : R →ₐ[O] R') [IsLocalHom φ] {x : R} (hx : x ∈ maximalIdeal R) :
    φ x ∈ maximalIdeal R' := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun hu => hx (isUnit_of_map_unit φ x hu)

private theorem inHat_push (φ : R →ₐ[O] R') [IsLocalHom φ] {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  unfold InHat CongOne EntIn at *
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  exact map_mem_max φ (H a b)

private theorem adicCont_push [TopologicalSpace D] (φ : R →ₐ[O] R') [IsLocalHom φ]
    {r : D →* GG (m := 3) (R := R)}
    (H : AdicCont (maximalIdeal R) r) : AdicCont (maximalIdeal R') (_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) := by
  unfold UpperTheory.V.UnitaryThreeInertia.AdicCont at *
  intro n
  have hle : ∀ x ∈ maximalIdeal R ^ n, (φ : R →+* R') x ∈ maximalIdeal R' ^ n := by
    intro x hx
    have h1 : Ideal.map (φ : R →+* R') (maximalIdeal R) ≤ maximalIdeal R' := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact map_mem_max φ hy
    have h2 : Ideal.map (φ : R →+* R') (maximalIdeal R ^ n) ≤ maximalIdeal R' ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono h1 n
    exact h2 (Ideal.mem_map_of_mem _ hx)
  let ψ : R ⧸ maximalIdeal R ^ n →+* R' ⧸ maximalIdeal R' ^ n :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (φ : R →+* R'))
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hle x hx))
  have hfun : (fun g => ((_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) g).mat.map (Ideal.Quotient.mk (maximalIdeal R' ^ n))) =
      (fun M => M.map ψ) ∘ (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) := by
    funext g
    ext a b
    simp only [Function.comp_apply, Matrix.map_apply, ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rfl
  rw [hfun]
  exact (H n).comp _

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.isPt_push :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ]
      (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
      [CommRing R'] [IsLocalRing R'] [Algebra O R'] (φ : R →ₐ[O] R') [IsLocalHom φ] (g₁ : Γ)
      (r : Γ →* GG (m := 3) (R := R)), F.IsPt g₁ r → F.IsPt g₁ (_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) := by
  intro O _ _ G Γ ι _ _ _ F R R' _ _ _ _ _ _ φ _ g₁ r hr
  have hmat : ∀ x : GG (m := 3) (R := R), ((GG.map (φ : R →+* R')) x).mat = x.mat.map φ := fun x => rfl
  have hpm : ∀ g, ((_root_.UpperTheory.V.UnitaryThreeInertia.push φ r) g).mat = (r g).mat.map φ := fun g => hmat (r g)
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, adicCont_push φ hr.cont⟩
  · have hm := hr.mult
    unfold HasMult at hm ⊢
    intro g
    exact hm g
  · intro g a b
    rw [Matrix.sub_apply, hpm, Matrix.map_apply, Matrix.map_apply, ← AlgHom.commutes φ, ← map_sub]
    apply map_mem_max φ
    have := hr.red g a b
    rwa [Matrix.sub_apply, Matrix.map_apply] at this
  · intro v
    have hv := hr.loc v
    unfold Frame.LocAt at hv ⊢
    obtain ⟨hT, hD, hU⟩ := hv
    unfold CondT CondD CondU at *
    have hcomp : (_root_.UpperTheory.V.UnitaryThreeInertia.push φ r).comp (F.loc v) = _root_.UpperTheory.V.UnitaryThreeInertia.push φ (r.comp (F.loc v)) := rfl
    rw [hcomp]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨k, hk, htr⟩ := hT h
      exact ⟨_, inHat_push φ hk, triIn_push φ htr⟩
    · obtain ⟨k, hk, hdi⟩ := hD h
      exact ⟨_, inHat_push φ hk, diagIn_push φ hdi⟩
    · intro s hs
      show (GG.map (φ : R →+* R')) ((r.comp (F.loc v)) s) = 1
      rw [hU h s hs, map_one]
  · obtain ⟨hatc, hz12, hz21⟩ := hr.norm
    refine ⟨?_, ?_, ?_⟩
    · rw [hpm, hatc, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · unfold zmat at hz12 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz12,
        map_zero]
    · unfold zmat at hz21 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz21,
        map_zero]
end
