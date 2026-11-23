module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitaryGlue

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_map {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) (s : R →+* R) (t : A →+* A)
    (h : ∀ z, p (s z) = t (p z)) (M : Matrix n n R) :
    (Formalism.UG.cT s M).map p = Formalism.UG.cT t (M.map p) := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem exists_glue {ι R : Type} [CommRing R] {A : ι → Type} [∀ i, CommRing (A i)] (p : ∀ i, R →+* A i)
    (hp : Function.Bijective fun (z : R) (i : ι) => p i z) (s : R →+* R) (t : ∀ i, A i →+* A i)
    (h : ∀ i z, p i (s z) = t i (p i z)) (J : Matrix n n R) (g : ∀ i, GL n (A i))
    (hg : ∀ i, g i ∈ Formalism.UG.UJ (t i) (J.map (p i))) :
    ∃ x ∈ Formalism.UG.UJ s J, ∀ i, Formalism.UG.bc (p i) x = g i := by
  have inj : ∀ M N : Matrix n n R, (∀ i, M.map (p i) = N.map (p i)) → M = N := by
    intro M N hMN
    ext a b
    exact hp.1 (funext fun i => congrFun (congrFun (hMN i) a) b)
  have sur : ∀ u : ∀ i, Matrix n n (A i), ∃ M : Matrix n n R, ∀ i, M.map (p i) = u i := by
    intro u
    choose M hM using fun a b => hp.2 (fun i => u i a b)
    exact ⟨Matrix.of M, fun i => by ext a b; exact congrFun (hM a b) i⟩
  obtain ⟨M, hM⟩ := sur fun i => (g i).1
  obtain ⟨N, hN⟩ := sur fun i => ((g i)⁻¹).1
  have h1 : ∀ i, (1 : Matrix n n R).map (p i) = 1 := fun i => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ fun i => ?_, inj _ _ fun i => ?_⟩, ?_, fun i => Units.ext (hM i)⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (p i) s (t i) (h i), hM]
    exact hg i

theorem exists_glue₂ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (p : R →+* A) (q : R →+* B)
    (e : R ≃+* A × B) (he : ∀ z, (e z).1 = p z ∧ (e z).2 = q z) (s : R →+* R) (t : A →+* A) (t' : B →+* B)
    (h : ∀ z, p (s z) = t (p z)) (h' : ∀ z, q (s z) = t' (q z)) (J : Matrix n n R) (g : GL n A) (g' : GL n B)
    (hg : g ∈ Formalism.UG.UJ t (J.map p)) (hg' : g' ∈ Formalism.UG.UJ t' (J.map q)) :
    ∃ x ∈ Formalism.UG.UJ s J, Formalism.UG.bc p x = g ∧ Formalism.UG.bc q x = g' := by
  have inj : ∀ M N : Matrix n n R, M.map p = N.map p → M.map q = N.map q → M = N := by
    intro M N h1 h2
    ext a b
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 a) b
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 a) b
  have sur : ∀ (u : Matrix n n A) (v : Matrix n n B), ∃ M : Matrix n n R, M.map p = u ∧ M.map q = v := by
    intro u v
    refine ⟨Matrix.of fun a b => e.symm (u a b, v a b), ?_, ?_⟩
    · ext a b
      simp [← (he _).1]
    · ext a b
      simp [← (he _).2]
  obtain ⟨M, hM, hM'⟩ := sur g.1 g'.1
  obtain ⟨N, hN, hN'⟩ := sur (g⁻¹).1 (g'⁻¹).1
  have h1 : (1 : Matrix n n R).map p = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (1 : Matrix n n R).map q = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ ?_ ?_, inj _ _ ?_ ?_⟩, ?_, Units.ext hM, Units.ext hM'⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM', hN', h2, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · rw [Matrix.map_mul, hM', hN', h2, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map p s t h, hM]
      exact hg
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map q s t' h', hM']
      exact hg'

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) : V.gram.det ≠ 0 := by
  apply GlobalTheory.RecDict.det_gram_ne_zero <;> assumption

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ z) =
      sigR S σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_map_inclR (f : R →ₐ[F] S) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (J.map (inclR R)).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = J.map (inclR S) := by
  ext i j
  simp [inclR]

end Tens

theorem exists_inf_fin {D : D7} (V : HSp D) (gi : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hi : gi ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram) (hf : gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) :
    ∃ g : GA D V, infHom V g = gi ∧ finHom V g = gf := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨x, hx, h1, h2⟩ := exists_glue₂
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom e he
    (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (map_sigR _ _) (map_sigR _ _)
    (JR (AF D.host.F) V.gram) gi gf
    (by rw [JR, map_map_inclR]; exact hi) (by rw [JR, map_map_inclR]; exact hf)
  exact ⟨⟨x, hx⟩, h1, h2⟩

theorem adelic_glue : ∀ (D : D7) (V : HSp D), (∀ gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram → ∃ g ∈ GfC V, finHom V g = gf) ∧ ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) → (∀ g : GA D V, (∀ τ, archM V (th τ) g = 1) → g ∈ GfC V) ∧ (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧ (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧ (∀ τ, Continuous (archM V (th τ))) ∧ ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) → ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ := by
  intro D V
  letI := D.host.cmStar
  refine ⟨fun gf hf => ?_, fun Ψ th hΨ hth => ?_⟩
  · obtain ⟨g, h1, h2⟩ := exists_inf_fin V 1 gf (one_mem _) hf
    exact ⟨g, h1, h2⟩
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  have hτ : ∀ (τ : D.host.E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := fun τ x =>
    IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : c ≠ 1 := fun h => IsCMField.complexConj_ne_one D.host.E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)
  obtain ⟨hex, hall⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E c D.sp.cm.deg2 hc
    D.sp.cm.totReal hτ
  choose θ₀ hθ₀ using hex
  classical
  let θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :=
    fun τ => if h : τ ∈ Ψ then th ⟨τ, h⟩ else θ₀ τ
  have hθt : ∀ τ : Ψ, θ τ.1 = th τ := fun τ => dif_pos τ.2
  obtain ⟨hcont, hconj, hbij⟩ := hall θ (fun τ => by
    by_cases h : τ ∈ Ψ
    · rw [hθt ⟨τ, h⟩]; exact hth ⟨τ, h⟩
    · have : θ τ = θ₀ τ := dif_neg h
      rw [this]; exact hθ₀ τ)
  have hb : Function.Bijective fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z := by
    have := hbij (Ψ : Set _) hΨ
    have e : (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z) =
        fun z (τ : Ψ) => θ τ.1 z := by
      funext z τ; rw [hθt]
    rw [e]; exact this
  have hinc : ∀ (τ : Ψ) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      (M.map (inclR (Ainf D.host.F))).map (th τ) = M.map τ.1 := by
    intro τ M
    ext i j
    exact (hth τ).1 _
  refine ⟨fun g hg => ?_, fun γ hγ => ?_, fun τ => ?_, fun u hu => ?_⟩
  · refine Units.ext (Matrix.ext fun a b => hb.1 (funext fun τ => ?_))
    have h1 := congrFun (congrFun (hg τ) a) b
    have h2 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).map (th τ) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    exact h1.trans (congrFun (congrFun h2 a) b).symm
  · obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have h1 : (matHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (AF D.host.F)) :=
      (congrArg Units.val h0).symm
    refine ⟨γ₀, fun τ => ?_, ?_⟩
    · rw [← hinc, ← map_map_inclR (fstA D.host.F), ← h1]; rfl
    · rw [← map_map_inclR (sndA D.host.F), ← h1]; rfl
  · obtain ⟨e, he, hec, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous (th τ) := hθt τ ▸ hcont τ.1
    have h2 : Continuous fun g : GA D V => (matHom V g).1 a b :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b
    have h3 : (fun g : GA D V => archM V (th τ) g a b) = fun g => th τ (e ((matHom V g).1 a b)).1 := by
      funext g
      rw [(he _).1]; rfl
    rw [h3]
    exact h1.comp (continuous_fst.comp (hec.comp h2))
  · have hdet : ∀ τ, (u τ).det ≠ 0 := by
      intro τ h0
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact gram_det_ne_zero V (τ.1.injective (by rw [map_zero, this]))
    obtain ⟨x, hx, hxu⟩ := exists_glue (A := fun _ : Ψ => ℂ) th hb (sigR _ D.sp.cm.sig) (fun _ => starRingEnd ℂ)
      (fun τ z => hθt τ ▸ hconj τ.1 z) (JR (Ainf D.host.F) V.gram)
      (fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (u τ) (hdet τ))
      (fun τ => by rw [JR, hinc]; exact hu τ)
    obtain ⟨g, h1, h2⟩ := exists_inf_fin V x 1 hx (one_mem _)
    refine ⟨g, h2, fun τ => ?_⟩
    rw [archM, h1]
    exact congrArg Units.val (hxu τ)

end GlobalTheory.UnitaryGlue
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isProjBy :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ L : LB A.left, L.IsLB → ∃ t : LB.Gen (Theta A L), t.IsGen := by
  intro k _ _ A _ hA hP L hL
  have := hA.comm
  have := hA.geomConnected
  have gi : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have conn : ConnectedSpace A.left := by
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have x : (Sp k : Scheme.{0}) := (default : PrimeSpectrum k)
    have h := A.hom.isConnected_preimage_singleton x
    have e : A.hom ⁻¹' {x} = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [e] at h
    exact connectedSpace_iff_univ.2 h
  have face : ∀ {Z : Over (Sp k)} (r : Z ⟶ G3 A) (i : Fin 3), r ≫ x3 A i = toUnit Z ≫ η[A] →
      Triv ((Theta A L).pull r.left) := fun {Z} r i h =>
    (CubeGen.triv_pull_iff L (thφ A (x3 A)) thε r.left).2
      (CubeGen.trivAt_of_formal hL _ (CubeGen.prod_face _ i (toUnit Z).left (congrArg (fun q => q.left) h)))
  exact GlobalTheory.T.theorem_of_cube_two_projective_factors k A A A η[A] η[A] η[A] hA.smooth hA.smooth hA.proper hA.proper hP hP gi gi conn
    (Theta A L) (DVR.linComb_isLB _ hL _ _) (face _ 0 (by simp [x3])) (face _ 1 (by simp [x3]))
    (face _ 2 (by simp [x3]))

end GlobalTheory
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.UnitarySplit

section Gen

open Formalism.UG

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem val_bc (p : R →+* A) (g : GL n R) : ((bc p g : GL n A) : Matrix n n A) = (g : Matrix n n R).map p := rfl

theorem mat_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {M N : Matrix n n R}
    (h1 : M.map p = N.map p) (h2 : M.map q = N.map q) : M = N := by
  ext i j
  exact hi _ _ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem gl_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {g h : GL n R}
    (h1 : bc p g = bc p h) (h2 : bc q g = bc q h) : g = h :=
  Units.ext (mat_ext p q hi (congrArg Units.val h1) (congrArg Units.val h2))

theorem gl_glue (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (hs : ∀ a b, ∃ x, p x = a ∧ q x = b) (a : GL n A) (b : GL n B) : ∃ g : GL n R, bc p g = a ∧ bc q g = b := by
  choose f hp hq using hs
  let G : Matrix n n A → Matrix n n B → Matrix n n R := fun M N => Matrix.of fun i j => f (M i j) (N i j)
  have Gp : ∀ M N, (G M N).map p = M := fun M N => by ext i j; simp [G, hp]
  have Gq : ∀ M N, (G M N).map q = N := fun M N => by ext i j; simp [G, hq]
  refine ⟨⟨G a.1 b.1, G (a⁻¹).1 (b⁻¹).1, ?_, ?_⟩, Units.ext (Gp _ _), Units.ext (Gq _ _)⟩ <;>
    apply mat_ext p q hi <;> simp [Matrix.map_mul, Gp, Gq]

theorem map_cond (p : R →+* A) (s : R →+* R) (t : A →+* A) (hc : ∀ x, p (s x) = t (p x)) (J g : Matrix n n R) :
    (cT s g * J * g).map p = cT t (g.map p) * J.map p * g.map p := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp [cT, hc]

theorem mem_iff (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (s : R →+* R) (t : A →+* A) (u : B →+* B) (hp : ∀ x, p (s x) = t (p x)) (hq : ∀ x, q (s x) = u (q x))
    (J : Matrix n n R) (g : GL n R) :
    g ∈ UJ s J ↔ bc p g ∈ UJ t (J.map p) ∧ bc q g ∈ UJ u (J.map q) := by
  change cT s g.1 * J * g.1 = J ↔ cT t (g.1.map p) * J.map p * g.1.map p = J.map p ∧
    cT u (g.1.map q) * J.map q * g.1.map q = J.map q
  rw [← map_cond p s t hp, ← map_cond q s u hq]
  exact ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun h => mat_ext p q hi h.1 h.2⟩

theorem mem_of_form (t : A →+* A) (J : Matrix n n A) (g : GL n A)
    (h : ∀ x y, hform t J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform t J x y) : g ∈ UJ t J := by
  change cT t g.1 * J * g.1 = J
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simp only [hform, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] at this
  rw [Finset.sum_comm] at this
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [this, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end Gen

section Tens

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem map_sig (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_JR (f : R →ₐ[F] R') {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (JR R J).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = JR R' J := by
  ext i j
  simp [JR, inclR]

end Tens

variable {D : D7}

theorem parts_inj (D : D7) (x y : AE D) (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem parts_surj (D : D7) (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : AE D, infPart D x = a ∧ finPart D x = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem mem_parts (V : HSp D) (g : GL (Fin V.rank) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram ↔
      Formalism.UG.bc (infPart D) g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram ∧
        Formalism.UG.bc (finPart D) g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have := mem_iff (infPart D) (finPart D) (parts_inj D) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig)
    (sigR _ D.sp.cm.sig) (map_sig _ _) (map_sig _ _) (JR _ V.gram) g
  rw [show (JR _ V.gram).map (infPart D) = JR _ V.gram from map_JR _ _,
    show (JR _ V.gram).map (finPart D) = JR _ V.gram from map_JR _ _] at this
  exact this

theorem ga_ext (V : HSp D) {g h : GA D V} (h1 : infHom V g = infHom V h) (h2 : finHom V g = finHom V h) : g = h :=
  Subtype.ext (gl_ext (infPart D) (finPart D) (parts_inj D) h1 h2)

theorem ga_glue (V : HSp D) (a : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (b : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (ha : a ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram)
    (hb : b ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) : ∃ g : GA D V, infHom V g = a ∧ finHom V g = b := by
  obtain ⟨g, h1, h2⟩ := gl_glue (infPart D) (finPart D) (parts_inj D) (parts_surj D) a b
  exact ⟨⟨g, (mem_parts V g).2 ⟨h1 ▸ ha, h2 ▸ hb⟩⟩, h1, h2⟩

theorem infHom_mem (V : HSp D) (g : GA D V) : infHom V g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).1

theorem finHom_mem (V : HSp D) (g : GA D V) : finHom V g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).2

theorem hermA_eq (V : HSp D) (x y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y =
      Formalism.UG.hform (sigR (Af D.host.F) D.sp.cm.sig) (JR (Af D.host.F) V.gram) y x := by
  unfold GlobalTheory.AdLat.hermA Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change x b * (JR (Af D.host.F) V.gram a b) * sigR (Af D.host.F) D.sp.cm.sig (y a) = _
  ring

theorem real_finite_split : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧ (∀ h : GA D V, h ∈ GinfC V → h ∈ GfC V → h = 1) ∧ (∀ g : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ (g.1 *ᵥ x) (g.1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) → ∃ k ∈ GfC V, finHom V k = g) ∧ ∀ g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E), g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram → ∃ a ∈ GinfC V, infHom V a = g := by
  intro D V
  refine ⟨fun h => ?_, fun a ha k hk => ?_, fun h h1 h2 => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V _ 1 (infHom_mem V h) (one_mem _)
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 _ (one_mem _) (finHom_mem V h)
    refine ⟨a, a2, k, k1, ga_ext V ?_ ?_⟩
    · rw [map_mul, a1, k1, mul_one]
    · rw [map_mul, a2, k2, one_mul]
  · have a2 : finHom V a = 1 := ha
    have k1 : infHom V k = 1 := hk
    refine ga_ext V ?_ ?_
    · rw [map_mul, map_mul, k1, mul_one, one_mul]
    · rw [map_mul, map_mul, a2, mul_one, one_mul]
  · have a2 : finHom V h = 1 := h1
    have k1 : infHom V h = 1 := h2
    exact ga_ext V (by rw [k1, map_one]) (by rw [a2, map_one])
  · have hm : g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
      mem_of_form _ _ g fun x y => by rw [← hermA_eq, ← hermA_eq, hg]
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 g (one_mem _) hm
    exact ⟨k, k1, k2⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V g 1 hg (one_mem _)
    exact ⟨a, a2, a1⟩

end GlobalTheory.UnitarySplit
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.principalGroup_acts_freely_on_flags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by
  first | exact @GlobalTheory.PrincFree.princ_free | exact GlobalTheory.PrincFree.princ_free | (intros; apply GlobalTheory.PrincFree.princ_free <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_root_near_one : ∀ (D : D7), ∀ W ∈ 𝓝 (1 : (AE D)ˣ), ∃ N ∈ 𝓝 (1 : (AE D)ˣ), ∀ u ∈ N, (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (u : AE D) = 1 → ∃ x ∈ W, (x : AE D) = (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by
  intro D
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  exact GlobalTheory.AdLat.RootNear.exists_root_near D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP

end GlobalTheory.Member
end
