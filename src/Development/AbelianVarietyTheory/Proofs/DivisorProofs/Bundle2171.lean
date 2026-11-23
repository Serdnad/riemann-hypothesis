module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_basis_kaehler_D {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension D k A] :
    ∃ (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]), ∀ i, B i = KaehlerDifferential.D k A (f i) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), P.basisKaehler.reindex e, fun i => by simp⟩

def derivHom {k A : Type} [CommRing k] [CommRing A] [Algebra k A] (δ : Derivation k A A) :
    A →+* DualNumber A where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, smul_eq_mul, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_comm, add_left_comm, add_assoc]

theorem snd_eq_sum_of_basis {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]) (hB : ∀ i, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K) (h : ∀ a, (θ (algebraMap k A a)).snd = 0) (s : A) :
    (θ s).snd = ∑ b, (θ (f b)).snd *
      (θ (((B.coord b).compDer (KaehlerDifferential.D k A)) s)).fst := by
  first
  | exact @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | (apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum ..)

theorem snd_eq_zero_of_isAlgebraic {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K]
    (φ : F →+* DualNumber K) (a : F) : (φ a).snd = 0 := by
  letI : Algebra ℚ (DualNumber K) := (φ.comp (algebraMap ℚ F)).toAlgebra
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (B := DualNumber K)
    (TrivSqZeroExt.fstHom K K K).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩ φ.toRatAlgHom
    ((algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)).toRatAlgHom
    (fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have e := DFunLike.congr_fun this a
  change φ a = _ at e
  rw [e]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_derivFrame (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X)
    (hp : p ∈ W) : ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  obtain ⟨V, hV, hx, hVW⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hp
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (dimFlag Dw)) M.str M.smooth
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(M.X, V)), p ∈ M.X.basicOpen (t : Γ(M.X, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(M.X, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).IsStandardSmoothOfRelativeDimension
      (dimFlag Dw) := by
    rw [← resG_comp_algX M.str (M.X.basicOpen_le (t : Γ(M.X, V)))]
    exact h₁
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (dimFlag Dw) c.F Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))) := h₂
  obtain ⟨f, B, hB⟩ := exists_basis_kaehler_D (D := dimFlag Dw) (k := c.F) (A := Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  refine ⟨_, IsAffineOpen.basicOpen hV _, fun b => derivHom ((B.coord b).compDer (KaehlerDifferential.D c.F _)),
    hxt, (M.X.basicOpen_le _).trans (hVW.trans le_rfl), fun b s => by simp [derivHom], fun K _ θ =>
    ⟨fun b => (θ (f b)).snd, fun s => ?_⟩⟩
  rw [snd_eq_sum_of_basis f B hB θ (fun a => snd_eq_zero_of_isAlgebraic (θ.comp (algebraMap c.F _)) a) s]
  simp [derivHom]

end GlobalTheory.CompHS
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (b : Γ(A.left, U)) (w : Fin g → ℂ), IsReg u.ex U fun z => fderiv ℂ (val u.ex U b) z w := by
  first | exact @GlobalTheory.CechPer.isReg_fderiv_val | exact GlobalTheory.CechPer.isReg_fderiv_val | (intros; apply GlobalTheory.CechPer.isReg_fderiv_val <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem two_mul_relDim_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  intro p _ D R _ b N K _ β o g hg
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : ℓ.Coprime p := (Nat.coprime_primes hℓ (Fact.out)).2 (by omega)
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hℓK : (ℓ : K) ≠ 0 := by
    have h := (b.unit ℓ hcop).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hx : spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap β =
      spMap ((algebraMap K (AlgebraicClosure K)).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨I, -⟩ := o.geom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
    ((algebraMap K (AlgebraicClosure K)).comp β) hx
  have hc := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (AlgebraicClosure K) o.A o.ab g hg ℓ hℓK
  let f : D.La →+ Additive (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ o.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev ℓ a)) fun a b => congrArg Additive.ofMul (I.add ℓ a b)
  have hk : f.ker = (nsmulAddMonoidHom ℓ : D.La →+ D.La).range := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact (I.ker ℓ hℓ0 hcop a).trans ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  have h2 : Nat.card {x : ptOver K (AlgebraicClosure K) ⟶ o.A // x ^ ℓ = 1} = ℓ ^ Module.finrank ℤ D.La := by
    rw [← AddSubgroup.index_range_nsmul, ← hk, AddSubgroup.index_ker]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => I.onto ℓ hℓ0 hcop u)
  rw [hc] at h2
  exact Nat.pow_right_injective hℓ.two_le h2

end GlobalTheory.UPel.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTDim

theorem card_torsion_of_ev {La Q : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] [Group Q]
    (ev : La → Q) (ℓ : ℕ) (hℓ : 0 < ℓ) (hadd : ∀ x y, ev (x + y) = ev x * ev y)
    (hker : ∀ x, ev x = 1 ↔ ∃ y, x = ℓ • y) (honto : ∀ q, q ^ ℓ = 1 ↔ ∃ x, ev x = q) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ La := by
  haveI : NeZero ℓ := ⟨by omega⟩
  let f : La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (ev x)) fun x y => by
    rw [hadd]; rfl
  let r := Module.finrank ℤ La
  let b := Module.finBasis ℤ La
  let g : La →+ (Fin r → ZMod ℓ) := AddMonoidHom.mk' (fun x i => ((b.repr x i : ℤ) : ZMod ℓ)) fun x y => by
    ext i; simp
  have hg : Function.Surjective g := by
    intro v
    choose w hw using fun i => ZMod.intCast_surjective (v i)
    refine ⟨b.equivFun.symm w, funext fun i => ?_⟩
    show ((b.repr (b.equivFun.symm w) i : ℤ) : ZMod ℓ) = v i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hw]
  have hk : f.ker = g.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    change Additive.ofMul (ev x) = 0 ↔ _
    rw [ofMul_eq_zero, hker]
    constructor
    · rintro ⟨y, rfl⟩
      ext i
      simp [g]
    · intro h
      have hd : ∀ i, (ℓ : ℤ) ∣ b.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun h i
      choose c hc using hd
      refine ⟨b.equivFun.symm c, b.ext_elem fun i => ?_⟩
      have hcy : b.repr (b.equivFun.symm c) i = c i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [map_nsmul, Finsupp.smul_apply, hcy, hc i, nsmul_eq_mul]
  have e1 : Nat.card {q : Q // q ^ ℓ = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun q => ?_)
    rw [honto, AddMonoidHom.mem_range]
    rfl
  rw [e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hk).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  simp [Nat.card_eq_fintype_card, r]

variable {p : ℕ} [Fact p.Prime]

theorem relDim {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) : SmoothOfRelativeDimension D.g o.A.hom := by
  have := o.ab.smooth
  choose n W hW hd using H1.exists_dim o.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension D.g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := AlgebraicClosure (o.A.left.residueField y)
  let z : Sp k ⟶ o.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (o.A.left.residueField y) k)) ≫ o.A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ o.A.hom
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let B := (Over.pullback x).obj o.A
  letI : (Over.pullback x).Monoidal := (Over.instBraidedPullback (f := x)).toMonoidal
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj x o.A o.ab
  obtain ⟨m, hm⟩ := GlobalTheory.AbVarRelDim.exists_relDim k B hB
  let z' : Sp k ⟶ pullback o.A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst o.A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ o.A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hℓp : (p + 1).Coprime p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have hℓk : ((p + 1 : ℕ) : k) ≠ 0 := by
    intro h0
    have := (b.unit (p + 1) hℓp).map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨I, -⟩ := o.geom k x β hβ
  have c1 := card_torsion_of_ev (I.ev (p + 1)) (p + 1) (by omega) (I.add (p + 1)) (I.ker (p + 1) (by omega) hℓp)
    (I.onto (p + 1) (by omega) hℓp)
  have c2 := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B m (p + 1) hB hm hℓk
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback o.A x) (𝟙 (Sp k)) x
    (Category.id_comp x).symm
  have c3 : Nat.card {q : 𝟙_ (Over (Sp k)) ⟶ B // q ^ (p + 1) = 1} =
      Nat.card {q : Over.mk x ⟶ o.A // q ^ (p + 1) = 1} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun q => by
      change q ^ (p + 1) = 1 ↔ e q ^ (p + 1) = 1
      rw [← map_pow, map_eq_one_iff e e.injective])
  have hr := D.rankLa
  have h2 : 2 * m = Module.finrank ℤ D.La :=
    Nat.pow_right_injective (by have := (Fact.out : p.Prime).two_le; omega : 2 ≤ p + 1) (by
      show (p + 1) ^ (2 * m) = (p + 1) ^ Module.finrank ℤ D.La
      rw [← c2, c3, c1])
  have hg : D.g = m := by
    show D.m * D.n * Module.finrank ℚ D.F / 2 = m
    omega
  rw [hg, ← e₁]
  exact hd y

theorem relDim_and_isLB : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
  fun _ _ _ _ _ _ _ _ _ o => ⟨relDim o, LB.isLB_pull o.isLB _⟩

end GlobalTheory.HTDim
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

open GlobalTheory.UPel.HT

theorem lieEigen_rank_cover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e,
    UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∀ τ : Fin D.a → (D.F →+* ℂ),
    (∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) →
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
    ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
      u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  first
  | exact @_root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif
  | exact _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif
  | (apply _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> assumption)
  | (intros; apply _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif ..)

end GlobalTheory.UPel.HT.LieType
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.WedgeSq

theorem exists_fin_sum_tmul {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (t : V ⊗[K] W) : ∃ (n : ℕ) (x : Fin n → V) (y : Fin n → W), t = ∑ i, x i ⊗ₜ[K] y i := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ ↦ a, fun _ ↦ b, by simp⟩
  | add s t hs ht =>
    obtain ⟨n, x, y, rfl⟩ := hs
    obtain ⟨m, x', y', rfl⟩ := ht
    exact ⟨n + m, Fin.append x x', Fin.append y y', by simp [Fin.sum_univ_add]⟩

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

variable {K : Type} [Field K]

theorem overPullbackStructureSheaf_cohomology_cup {Y A : Over (Sp K)} (f : Y ⟶ A) (a b : HO1 A.hom) :
    structureSheafH2Pullback f (cup (OAff A.hom) a b) = cup (OAff Y.hom) (pO1 f a) (pO1 f b) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 K K A.left Y.left A.hom Y.hom (RingHom.id K) f.left (ovw f)).1 a b

variable (A : Over (Sp K)) [GrpObj A]

abbrev mixed : HO1 A.hom →ₗ[K] HO1 A.hom →ₗ[K] HO2 (A ⊗ A).hom :=
  (cup (OAff (A ⊗ A).hom)).compl₁₂ (pO1 (fst A A)) (pO1 (snd A A))

theorem defect_eq (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom) :
    structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t) - structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      - structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      = TensorProduct.lift (mixed A) (t - TensorProduct.comm K _ _ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.lift.tmul, TensorProduct.comm_tmul, map_sub, overPullbackStructureSheaf_cohomology_cup, hp a, hp b, map_add (f := _),
      LinearMap.add_apply, LinearMap.compl₁₂_apply]
    rw [GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm K _ (OAff (A ⊗ A).hom) (pO1 (snd A A) a) (pO1 (fst A A) b)]
    abel
  | add s t hs ht =>
    have e : s + t - TensorProduct.comm K _ _ (s + t)
        = (s - TensorProduct.comm K _ _ s) + (t - TensorProduct.comm K _ _ t) := by
      rw [map_add (f := _)]; abel
    rw [e, map_add (TensorProduct.lift (mixed A)), ← hs, ← ht]
    simp only [map_add (f := _)]
    abel

theorem mixed_injective [IsSeparated A.hom] [QuasiCompact A.hom] (u : HO1 A.hom ⊗[K] HO1 A.hom)
    (hu : TensorProduct.lift (mixed A) u = 0) : u = 0 := by
  obtain ⟨n, x, y, rfl⟩ := exists_fin_sum_tmul u
  refine GlobalTheory.T.kunneth_cup_tensor_injective K A A inferInstance inferInstance inferInstance inferInstance n x y ?_

  simpa [map_sum] using hu

theorem symm_of_prim [IsSeparated A.hom] [QuasiCompact A.hom] (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom)
    (ht : structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t)
      = structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
        + structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)) :
    TensorProduct.comm K _ _ t = t := by
  have h0 := defect_eq A hp t
  rw [ht, add_sub_cancel_left, sub_self] at h0
  exact (sub_eq_zero.1 (mixed_injective A _ h0.symm)).symm

end GlobalTheory.AbCoh.WedgeSq


open GlobalTheory.AbCoh.WedgeSq in
theorem GlobalTheory.AbCoh.wedgeO_noPrimO2 : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A := by
  intro K _ _ A _ g hab hsm
  haveI : IsProper A.hom := hab.proper
  haveI hsep : IsSeparated A.hom := inferInstance
  haveI hqc : QuasiCompact A.hom := inferInstance
  obtain ⟨-, hprim, -⟩ := GlobalTheory.T.abelian_variety_h1_axes_primitive_rank K A g hab hsm
  obtain ⟨n, D, hD, hcov⟩ := GlobalTheory.AbCoh.WedgeSq.exists_fin_affine_cover A.hom
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D hsep hD hcov
  obtain ⟨hfin, h1, h2⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hab hsm (Fin n) D hD hcov
  haveI := hfin 1
  haveI := hfin 2
  haveI : Module.Finite K (HO1 A.hom) := Module.Finite.equiv e1.symm
  haveI : Module.Finite K (HO2 A.hom) := Module.Finite.equiv e2.symm
  have hdim : Module.finrank K (HO2 A.hom) ≤ (Module.finrank K (HO1 A.hom)).choose 2 := by
    rw [e2.finrank_eq, e1.finrank_eq, h1]; exact h2
  have hrel : ∀ t : HO1 A.hom ⊗[K] HO1 A.hom, TensorProduct.lift (cup (OAff A.hom)) t = 0 →
      TensorProduct.comm K _ _ t = t := fun t ht ↦ symm_of_prim A hprim t (by simp [ht])
  obtain ⟨hw, hsurj, hsym⟩ := GlobalTheory.T.exteriorSquare_of_symmetric_tensor_relations K (HO1 A.hom) (HO2 A.hom) (cup (OAff A.hom)) hdim hrel
  refine ⟨hw, fun z hz ↦ ?_⟩
  obtain ⟨t, rfl⟩ := hsurj z
  exact hsym t (symm_of_prim A hprim t hz)
end
end
