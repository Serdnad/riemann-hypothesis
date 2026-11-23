module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDet
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle019
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lc_of_ker {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    (φ : G →* M) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) =
      ((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) - (ρ g).map (algebraMap A A[X])).det := by
  change (GDet.repAlg ρ A[X] _).det = _
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [GDet.repAlg]

private theorem cont_ofChars {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : Fin n → G →* Aˣ) (h : ∀ i, IsOpen ((χ i).ker : Set G)) (I : Ideal A) : (GDet.ofChars χ).IsCont I := by
  intro i N
  have h1 : IsLocallyConstant fun g j => χ j g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun j => (lc_of_ker (χ j) (h j)).eventually_eq x
    exact (Filter.eventually_all.2 this).mono fun y hy => funext hy
  have h2 := h1.comp fun v : Fin n → Aˣ => Ideal.Quotient.mk (I ^ N) ((-1) ^ i *
    (((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) -
      (Matrix.diagonal fun j => (v j : A)).map (algebraMap A A[X])).det).coeff (n - i))
  convert h2 using 1
  funext g
  simp [GDet.lam, GDet.ofChars, chi_ofRep, GDet.diagRep]

private theorem fin_field (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ)
    (hP : PhiCond (Γ := G) l) (ho : ∀ i, IsOpen ((χ i).ker : Set G)) (hi : Function.Injective χ) :
    Module.Finite k ((GDet.ofChars χ).CHQuot ∅) := by
  have hinj : Function.Injective (residue k) := (residue k).injective
  haveI : Finite (ResidueField k) := Finite.of_surjective _ residue_surjective
  haveI : CharP (ResidueField k) l := charP_of_injective_ringHom hinj l
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  let u : kˣ →* (ResidueField k)ˣ := Units.map (residue k).toMonoidHom
  have hu : Function.Injective u := Units.map_injective hinj
  let χ' : Fin n → G →* (ResidueField k)ˣ := fun i => u.comp (χ i)
  have ho' : ∀ i, IsOpen ((χ' i).ker : Set G) := fun i => by
    have : (χ' i).ker = (χ i).ker := MonoidHom.ker_comp_of_injective _ _ hu
    rw [this]
    exact ho i
  have hi' : Function.Injective χ' := fun i j hij =>
    hi (MonoidHom.ext fun g => hu (DFunLike.congr_fun hij g))
  obtain ⟨h, hm⟩ := exists_multFree_of_phiCond_of_injective_chars l χ' hP ho' hi'
  have hmap : (GDet.ofChars χ).map (residue k) = GDet.ofChars χ' := by
    unfold GDet.ofChars
    rw [(d_gmap (GDet.ofRep (GDet.diagRep χ))).2.2.2]
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [GDet.diagRep, χ', u]
    · simp [GDet.diagRep, hab]
  exact (finE (GDet.ofChars χ) χ' (cont_ofChars χ ho _) hmap hm ∅).2.1

theorem UpperTheory.V.CA.univDet_mf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* (ResidueField O)ˣ), PhiCond (Γ := G) l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G), IsUnivDet O (GDet.ofChars χ) D := by
  intro l _ O _ _ _ _ _ _ n G _ _ _ _ _ χ hP ho hi
  exact univDet l O (GDet.ofChars χ) hP (cont_ofChars χ ho _) (fin_field l χ hP ho hi)
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lift_surj {B E E' P : Type} [CommRing B] [Ring E] [Ring E'] [Ring P] [Algebra B E] [Algebra B E']
    [Algebra B P] (q : E →ₐ[B] E') (hq : Function.Surjective q) (ρ : E →ₐ[B] P) (h : ∀ x, q x = 0 → ρ x = 0) :
    ∃ π : E' →ₐ[B] P, ∀ x, π (q x) = ρ x := by
  have key : ∀ x y, q x = q y → ρ x = ρ y := fun x y hxy =>
    sub_eq_zero.1 (by rw [← map_sub]; exact h _ (by rw [map_sub, hxy, sub_self]))
  choose s hs using hq
  have hq' : ∀ x, ρ (s (q x)) = ρ x := fun x => key _ _ (hs _)
  refine ⟨⟨⟨⟨⟨fun y => ρ (s y), ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, fun r => ?_⟩, hq'⟩
  · rw [← map_one q, hq', map_one]
  · change ρ (s (a * b)) = ρ (s a) * ρ (s b)
    rw [← map_mul]
    exact key _ _ (by rw [map_mul, hs, hs, hs])
  · change ρ (s 0) = 0
    rw [← map_zero q, hq', map_zero]
  · change ρ (s (a + b)) = ρ (s a) + ρ (s b)
    rw [← map_add (f := _)]
    exact key _ _ (by rw [map_add (f := _), hs, hs, hs])
  · change ρ (s (algebraMap B E' r)) = _
    rw [← q.commutes, hq', ρ.commutes]

theorem UpperTheory.V.CA.finE_gma :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → ∀ Z : Set (MonoidAlgebra B G), (∀ z ∈ Z, D.Kills z) → ∃ (DE : Det n B (D.CHQuot Z)) (π : D.CHQuot Z →ₐ[B] (Fin n → ResidueField B)) (e : Fin n → D.CHQuot Z), DE.pull (D.toQuot Z) = D.toDet ∧ IsGMA DE e ∧ Function.Surjective π ∧ (∀ g i, π (D.toQuot Z (MonoidAlgebra.single g 1)) i = χ i g) ∧ (∀ x, π x = 0 ↔ x ∈ Ring.jacobson (D.CHQuot Z)) ∧ (∀ i, π (e i) = Pi.single i 1) ∧ ∀ x, (DE.chi x).map (residue B) = ∏ i, (X - C (π x i)) := by
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hred hm Z hZ
  obtain ⟨DE, hCH, hDE⟩ := d_quotDet D hc Z hZ
  obtain ⟨π0, hs0, hg0, -, hchi0⟩ := f_chars χ hm.inj
  let ρ : MonoidAlgebra B G →ₐ[B] (Fin n → ResidueField B) :=
    (π0.restrictScalars B).comp (MonoidAlgebra.mapAlgHom G (Algebra.ofId B (ResidueField B)))
  have hρ : ∀ x, ρ x = π0 (MonoidAlgebra.mapRingHom G (residue B) x) := fun x => rfl
  have hchi : ∀ x, (DE.chi (D.toQuot Z x)).map (residue B) = ∏ i, (X - C (ρ x i)) := fun x => by
    rw [← (d_pull DE (D.toQuot Z)).1, hDE, (d_toDet D x).1, ← ((d_gmap D).2.2.1 (residue B) x).1, hred, hchi0, hρ]
  have hsurj : Function.Surjective (D.toQuot Z) := fun q => Quotient.exists_rep q
  have hker : ∀ x, D.toQuot Z x = 0 → ρ x = 0 := fun x hx => by
    have h1 := hchi x
    rw [hx, ← map_zero (D.toQuot Z), hchi 0, map_zero] at h1
    funext i
    have h2 := congrArg (eval (ρ x i)) h1
    rw [eval_prod, eval_prod, Finset.prod_eq_zero (f := fun j => eval (ρ x i) (X - C (ρ x j)))
      (Finset.mem_univ i) (by simp)] at h2
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2
    simpa using hj
  obtain ⟨π, hπ⟩ := lift_surj (D.toQuot Z) hsurj ρ hker
  have hmap : ∀ y : MonoidAlgebra (ResidueField B) G, ∃ x, MonoidAlgebra.mapRingHom G (residue B) x = y := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | single g r =>
      obtain ⟨c, rfl⟩ := residue_surjective r
      exact ⟨MonoidAlgebra.single g c, MonoidAlgebra.mapRingHom_single _ _ _⟩
  have hπs : Function.Surjective π := fun v => by
    obtain ⟨y, rfl⟩ := hs0 v
    obtain ⟨x, rfl⟩ := hmap y
    exact ⟨D.toQuot Z x, by rw [hπ, hρ]⟩
  have hchiE : ∀ x, (DE.chi x).map (residue B) = ∏ i, (X - C (π x i)) := fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hπ, hchi]
  haveI : IsLocalHom (algebraMap B (ResidueField B)) := inferInstanceAs (IsLocalHom (residue B))
  obtain ⟨hj, e, he, hπe⟩ := f_gma DE π hCH hπs hchiE
  refine ⟨DE, π, e, hDE, he, hπs, fun g i => ?_, hj, hπe, hchiE⟩
  rw [hπ, hρ, MonoidAlgebra.mapRingHom_single, map_one, hg0]
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.stable_field :
    ∀ {n : ℕ} {A G κ κ' : Type} [CommRing A] [Group G] [Field κ] [IsAlgClosed κ] [Field κ'] [IsAlgClosed κ'] (D : GDet n A G) (f : A →+* κ) (f' : A →+* κ'), RingHom.ker f = RingHom.ker f' → (∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ) → ∃ ρ : G →* Matrix (Fin n) (Fin n) κ', UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f' = GDet.ofRep ρ := by
  intro n A G κ κ' _ _ _ _ _ _ D f f' hker ⟨ρ, hρ, hD⟩
  obtain ⟨ρ', hD'⟩ : ∃ ρ' : G →* Matrix (Fin n) (Fin n) κ', D.map f' = GDet.ofRep ρ' := by
    obtain ⟨r, -, hr⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed (D.map f').toDet
    let ρ' := r.toMonoidHom.comp (MonoidAlgebra.of κ' G)
    have hrep : GDet.repAlg ρ' κ' = r := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, ρ', MonoidAlgebra.lift_single]
      · ext
    refine ⟨ρ', Eq.symm ?_⟩
    suffices h : (GDet.ofRep ρ').toDet = (D.map f').toDet by
      rw [← GDet.ofDet_toDet (GDet.ofRep ρ'), h, GDet.ofDet_toDet]
    rw [← hr, ← hrep]
    refine Det.ext' fun S _ _ x => ?_
    change (GDet.repAlg ρ' S (ofT κ' G S x)).det = (Det.repS (GDet.repAlg ρ' κ') S x).det
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
      | single g a => ext i j; simp [GDet.repAlg]
  refine ⟨ρ', ?_, hD'⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact (UpperTheory.V.AlgebraTools.Det.matIrrIff ⊤ ρ').2 (Subsingleton.elim _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htrace (K : Type) [Field K] (φ : A →+* K) (τ : G →* Matrix (Fin n) (Fin n) K)
      (hτ : D.map φ = GDet.ofRep τ) (g : G) :
      (τ g).trace = φ (D.tr (MonoidAlgebra.single g 1)) := by
    have hmap : (D.map φ).chi (MonoidAlgebra.single g 1) =
        (D.chi (MonoidAlgebra.single g 1)).map φ := by
      let _ : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let ψ : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with commutes' := fun _ => Polynomial.map_C φ }
      have hψ (x : A[X]) : ψ x = x.map φ := rfl
      have h := D.nat A[X] K[X] ψ (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)
      simpa only [GDet.chi, GDet.map, map_sub, MonoidAlgebra.mapRingHom_single,
        AlgHom.coe_toRingHom, hψ, Polynomial.map_X, map_one] using h
    have hchi : (GDet.ofRep τ).chi (MonoidAlgebra.single g 1) = (τ g).charpoly := by
      simp only [GDet.chi, MonoidAlgebra.mapRingHom_single, map_one]
      change (GDet.repAlg τ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)).det = _
      rw [map_sub, Matrix.charpoly]
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [GDet.repAlg, hij]
    rw [hτ, hchi] at hmap
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap]
    simp [GDet.tr, GDet.lam]
  let H : Subgroup G := ⊤
  obtain ⟨U, -, hU⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
    (fun g : H => D.tr (MonoidAlgebra.single (g : G) 1))
  let p : PrimeSpectrum A := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  have hp : p ∈ U := (hU κ f (ρ.comp H.subtype) p rfl (fun g => htrace κ f ρ hD g)).2
    ((UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ).1 hρ)
  exact (UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ').2
    ((hU κ' f' (ρ'.comp H.subtype) p hker (fun g => htrace κ' f' ρ' hD' g)).1 hp)
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.groupDet_exists_semisimple_representation :
    ∀ {n : ℕ} {k G : Type} [Field k] [IsAlgClosed k] [Group G] (D : GDet n k G), ∃ ρ : G →* Matrix (Fin n) (Fin n) k, IsSemisimpleRing (GDet.repAlg ρ k).range ∧ GDet.ofRep ρ = D ∧ ∀ y, D.Kills y ↔ GDet.repAlg ρ k y = 0 := by
  intro n k G _ _ _ D
  obtain ⟨r, hss, hD⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed D.toDet
  let ρ : G →* Matrix (Fin n) (Fin n) k := (r : MonoidAlgebra k G →* Matrix (Fin n) (Fin n) k).comp
    (MonoidAlgebra.of k G)
  have hr : GDet.repAlg ρ k = r := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [GDet.repAlg, ρ, MonoidAlgebra.lift_single]
    · ext
  refine ⟨ρ, hr ▸ hss, ?_, fun y => ?_⟩
  · have hrep : (GDet.ofRep ρ).toDet = Det.ofRep (Fintype.card_fin n) (GDet.repAlg ρ k) := by
      refine Det.ext' fun S _ _ x => ?_
      change (GDet.repAlg ρ S (ofT k G S x)).det = (Det.repS (GDet.repAlg ρ k) S x).det
      congr 1
      induction x with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul s y =>
        rw [ofT_tmul, Det.repS_tmul, map_smul]
        congr 1
        induction y using MonoidAlgebra.induction_linear with
        | zero => ext i j; simp
        | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
        | single g a => ext i j; simp [GDet.repAlg]
    rw [← GDet.ofDet_toDet (GDet.ofRep ρ), hrep, hr, hD, GDet.ofDet_toDet]
  · have hval (S : Type) [CommRing S] [Algebra k S] (h : S ⊗[k] MonoidAlgebra k G) :
        D.toDet.D S (1 + h * (1 ⊗ₜ y)) =
          D.D S (1 + ofT k G S h * MonoidAlgebra.mapRingHom G (algebraMap k S) y) := by
      change D.D S (ofT k G S (1 + h * (1 ⊗ₜ y))) = _
      rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
    have hkills : D.toDet.Kills y ↔ D.Kills y := by
      constructor
      · intro hk S _ _ h
        have hh := hk S (toT k G S h)
        rwa [hval, ofT_toT] at hh
      · intro hk S _ _ h
        rw [hval]
        exact hk S _
    rw [← hkills, ← (d_ker D.toDet y).1, ← hD, d_ker_ss _ r hss, hr]
end
