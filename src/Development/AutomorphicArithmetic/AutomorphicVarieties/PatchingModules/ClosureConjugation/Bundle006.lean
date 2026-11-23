module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle004
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem conj_prod_zero {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (M : Fin n → GL (Fin n) R)
    (c : Fin n → R) (h1 : ∀ k i j, j < i → (w⁻¹ * M k * w : GL (Fin n) R) i j = 0)
    (h2 : ∀ k, (w⁻¹ * M k * w : GL (Fin n) R) k k = c k) :
    (List.ofFn fun k => (M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  classical
  let f : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun A => (↑w⁻¹ : Matrix (Fin n) (Fin n) R) * A * ↑w
      map_one' := by simp
      map_mul' := fun A B => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑w : Matrix (Fin n) (Fin n) R) (↑w⁻¹ : Matrix (Fin n) (Fin n) R)]
        simp }
  have hf : ∀ k, f ((M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)) =
      ((w⁻¹ * M k * w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R) := by
    intro k
    simp [f, Matrix.mul_sub, Matrix.sub_mul, Units.val_mul]
  have key : f (List.ofFn fun k => (M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
    rw [map_list_prod, List.map_ofFn]
    apply tri_prod_zero
    · intro k i j hij
      simp only [Function.comp_apply, hf, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_lt hij).symm, smul_zero, sub_zero]
      exact h1 k i j hij
    · intro k
      simp only [Function.comp_apply, hf, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [h2 k, sub_self]
  have back : ∀ A : Matrix (Fin n) (Fin n) R,
      A = (↑w : Matrix (Fin n) (Fin n) R) * f A * (↑w⁻¹ : Matrix (Fin n) (Fin n) R) := by
    intro A
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, ← Matrix.mul_assoc]
    simp [Matrix.mul_assoc]
  rw [back (List.ofFn _).prod, key]
  simp

private theorem ch_prod_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c : Fin n → R)
    (h : M.charpoly = ∏ i, (X - C (c i))) :
    (List.ofFn fun k => M - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  classical
  have e : (List.ofFn fun k => M - c k • (1 : Matrix (Fin n) (Fin n) R)).prod =
      aeval M (∏ i, (X - C (c i))) := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    congr 1
    congr 1
    funext k
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e, ← h, aeval_self_charpoly]

theorem UpperTheory.V.Pa.rep_gens :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ z ∈ P.gens, P.rep z = 0 := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P z hz
  have hs : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) =
      P.f b • ((x.ρ (h.p₀ g) : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) := by
    intro g b
    simp [OoPt.rep, GDet.repAlg, mat]
  have hfac : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 b) =
      ((x.ρ (h.p₀ g) : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) - P.f b • (1 : Matrix (Fin n) (Fin n) x.A) := by
    intro g b
    rw [map_sub, hs, hs]
    simp
  have hst : ∀ y, P.rep y = 0 → P.rep (G.frame.star O B n y) = 0 := by
    intro y hy
    rw [rep_star, hy, Matrix.transpose_zero]
  have hL : ∀ (m : ℕ) (F : Fin m → MonoidAlgebra B G.G₀),
      P.rep (List.ofFn F).prod = (List.ofFn fun i => P.rep (F i)).prod := by
    intro m F
    rw [map_list_prod, List.map_ofFn]
    rfl
  have hφ : ∀ v (g : L.Gv v), h.p₀ (G.frame.φ v g) = G0.frame.φ v g := by
    intro v g
    exact Subtype.ext (h.φ v g)
  have kOrd : ∀ v g, P.rep (G.frame.oEl v (u.ψ v) g) = 0 := by
    intro v g
    rw [GFrame.oEl, hL]
    simp only [hfac]
    apply conj_prod_zero (x.w v) (fun i => x.ρ (h.p₀ (G.frame.φ v (g i)))) (fun i => P.f ↑(u.ψ v i (g i)))
    · intro k i j hij
      rw [hφ]
      exact (x.tri v (g k)).1 i j hij
    · intro k
      rw [hφ, (x.tri v (g k)).2 k, ← P.maps.2 v k]
      rfl
  have kI : ∀ w, ∀ g ∈ r.Ip w, P.rep (MonoidAlgebra.single g 1) = 1 := by
    intro w g hg
    rw [P.Ip w] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    have e : h.p₀ (G.φu w a) = G0.φu w a := Subtype.ext (h.φu w a)
    have hin : G0.φu w a ∈ G0.frame.Iu w := ⟨a, ha, rfl⟩
    rw [hs, e, x.ine w _ hin]
    simp
  have kq1 : ∀ j, P.rep (q1El (P.ph j) (P.U j)) = 0 := by
    intro j
    rw [q1El, hL]
    simp only [hfac]
    exact ch_prod_zero _ _ (P.eig j)
  have kq2 : ∀ j i, P.rep (q2El (P.ph j) (P.ta j) (P.U j) i (P.y j i)) = 0 := by
    intro j i
    rw [q2El, map_mul, map_sub, map_sub, hs, hs, P.p_ta j, P.f_y j i]
    simp
  rcases hz with hz | hz
  · rcases hz with ⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩
    · exact kOrd v g
    · exact hst _ (kOrd v g)
    · rw [map_sub, kI w g hg, map_one, sub_self]
    · rw [map_sub, rep_star, kI w g hg, map_one, Matrix.transpose_one, sub_self]
  · rcases hz with ⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩
    · exact kq1 j
    · exact hst _ (kq1 j)
    · exact kq2 j i
    · exact hst _ (kq2 j i)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem gdet_eq_ofRep {n : ℕ} {A G E S : Type} [CommRing A] [Group G] [Ring E] [Algebra A E] [CommRing S]
    [Algebra A S] (D : GDet n A G) (DE : Det n A E) (ι : MonoidAlgebra A G →ₐ[A] E) (hp : DE.pull ι = D.toDet)
    (hch : DE.IsCH) (ep : Fin n → E) (he : CompleteOrthogonalIdempotents ep)
    (h1 : ∀ i, DE.D A[X] (1 + X ⊗ₜ ep i) = 1 + X) (φ : E →ₐ[A] Matrix (Fin n) (Fin n) S)
    (hφ : ∀ i, φ (ep i) = single i i 1) (vr : G →* Matrix (Fin n) (Fin n) S)
    (hvr : ∀ γ, vr γ = φ (ι (MonoidAlgebra.single γ 1))) :
    D.map (algebraMap A S) = GDet.ofRep vr := by
  refine GDet.ext fun T _ _ y => ?_
  letI : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
  haveI : IsScalarTower A S T := .of_algebraMap_eq fun _ => rfl
  let ψ : T ⊗[A] E →ₐ[T] Matrix (Fin n) (Fin n) T :=
    Algebra.TensorProduct.lift (Algebra.ofId T _) ((IsScalarTower.toAlgHom A S T).mapMatrix.comp φ)
      fun s _ => Algebra.commute_algebraMap_left s _
  have hψ : ∀ (t : T) (z : E), ψ (t ⊗ₜ z) = t • (φ z).map (algebraMap S T) := fun t z =>
    (Algebra.TensorProduct.lift_tmul _ _ _ t z).trans (Algebra.smul_def _ _).symm
  have hD : ∀ w : T ⊗[A] E, DE.D T w = (ψ w).det := by
    intro w
    obtain ⟨k, t, z, rfl⟩ := TensorProduct.exists_sum_tmul_eq w

    rw [d_gma_det DE ep hch he h1 S φ hφ T t z, map_sum]
    simp only [hψ]
  have h2 : D.D T y = DE.D T (Algebra.TensorProduct.map (AlgHom.id T T) ι (toT A G T y)) := by
    have h3 : D.D T y = D.toDet.D T (toT A G T y) := (congrArg (D.D T) (ofT_toT (A := A) y)).symm
    rw [h3, ← hp]
    rfl
  change D.D T y = (GDet.repAlg vr T y).det
  rw [h2, hD]
  clear h2
  congr 1
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s =>
    rw [toT_single, Algebra.TensorProduct.map_tmul, hψ, ← hvr]
    simp [GDet.repAlg]

theorem UpperTheory.V.Pa.gr_det :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), CompleteOrthogonalIdempotents ep → (∀ i, H.DE.D Bh[X] (1 + X ⊗ₜ ep i) = 1 + X) → ∀ vr : G.G₀ →* Matrix (Fin n) (Fin n) g.AA, (∀ γ, vr γ = g.φ (H.ι (MonoidAlgebra.single γ 1))) → D.map ((algebraMap Bh g.AA).comp (algebraMap B Bh)) = GDet.ofRep vr := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g he h1 vr hvr
  rw [← (d_gmap D).2.1]
  exact gdet_eq_ofRep _ H.DE H.ι H.pull H.ch ep he h1 g.φ g.φ_ep vr hvr
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem quot_ss {B Bh E κ Γ : Type} [CommRing B] [CommRing Bh] [Algebra B Bh] [Ring E] [Algebra Bh E]
    [Field κ] [Algebra Bh κ] [Group Γ] (I : Set (MonoidAlgebra B Γ))
    (ι : MonoidAlgebra Bh Γ →ₐ[Bh] E) (surj : Function.Surjective ι)
    (ker : ∀ y, ι y = 0 → y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I))
    [IsSemisimpleRing (κ ⊗[Bh] E)] :
    IsSemisimpleRing (TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I)).ringCon.Quotient := by
  set J := TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I) with hJ
  let π : MonoidAlgebra κ Γ →+* J.ringCon.Quotient := J.ringCon.mk'
  have hπ : ∀ z, z ∈ J → π z = 0 := by
    intro z hz
    rw [← map_zero π]
    exact (RingCon.eq _).2 ((TwoSidedIdeal.mem_iff _ _).1 hz)
  let ψ0 : MonoidAlgebra Bh Γ →+* J.ringCon.Quotient :=
    π.comp (MonoidAlgebra.mapRingHom Γ (algebraMap Bh κ))
  have hk : RingHom.ker ι.toRingHom ≤ RingHom.ker ψ0 := by
    intro y hy
    have h1 := ker y hy
    have h2 : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I) ≤ TwoSidedIdeal.ker ψ0 := by
      rw [TwoSidedIdeal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
      apply hπ
      apply TwoSidedIdeal.subset_span
      refine ⟨z, hz, ?_⟩
      ext a
      simp
    exact (TwoSidedIdeal.mem_ker _).1 (h2 h1)
  let ψ : E →+* J.ringCon.Quotient := ι.toRingHom.liftOfSurjective surj ⟨ψ0, hk⟩
  have hψ : ∀ y, ψ (ι y) = ψ0 y := fun y => RingHom.liftOfSurjective_comp_apply ι.toRingHom surj ⟨ψ0, hk⟩ y
  let ψa : E →ₐ[Bh] J.ringCon.Quotient :=
    { ψ with
      commutes' := fun b => by
        change ψ (algebraMap Bh E b) = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        rw [← ι.commutes, hψ]
        change π _ = _
        congr 1
        simp [MonoidAlgebra.coe_algebraMap] }
  let ka : κ →ₐ[Bh] J.ringCon.Quotient :=
    { π.comp (algebraMap κ (MonoidAlgebra κ Γ)) with
      commutes' := fun b => by
        change π _ = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        congr 1 }
  have hc : ∀ a y, Commute (ka a) (ψa y) := by
    intro a y
    obtain ⟨y, rfl⟩ := surj y
    change Commute (π (algebraMap κ _ a)) (ψ (ι y))
    rw [hψ]
    exact Commute.map (Algebra.commutes a _) π
  let Φ := Algebra.TensorProduct.lift ka ψa hc
  refine RingHom.isSemisimpleRing_of_surjective Φ.toRingHom ?_
  intro w
  obtain ⟨w, rfl⟩ : ∃ z, π z = w := J.ringCon.mk'_surjective w
  induction w using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | single m a =>
    refine ⟨a ⊗ₜ ι (MonoidAlgebra.single m 1), ?_⟩
    change Φ _ = _
    rw [Algebra.TensorProduct.lift_tmul]
    change π (algebraMap κ _ a) * ψ (ι _) = _
    rw [hψ]
    change π _ * π _ = _
    rw [← map_mul]
    congr 1
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.single_mul_single]

theorem UpperTheory.V.Pa.gr_thick :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), ∀ Q : Ideal Bh, Q.IsPrime → NonSS I (algebraMap B Bh) Q → Module.annihilator Bh g.N ≤ Q := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g Q _ hQ s hs
  obtain ⟨κ, _, f, hf, hns⟩ := hQ
  by_contra hsQ
  letI : Algebra Bh κ := f.toAlgebra
  have hs0 : algebraMap Bh κ s ≠ 0 := fun h0 => hsQ (hf ▸ (RingHom.mem_ker.2 h0 : s ∈ RingHom.ker f))
  haveI := UpperTheory.V.Pa.gr_ss g κ s hs0 hs
  exact hns (quot_ss (κ := κ) I H.ι H.surj (fun y hy => (H.ker y).1 hy))
end
