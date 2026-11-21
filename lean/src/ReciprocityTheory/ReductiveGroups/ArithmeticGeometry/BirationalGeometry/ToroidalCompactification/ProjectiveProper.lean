import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isProper_str (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  haveI : IsScalarTower R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hf : Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have hP : IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) := by
    infer_instance

  have hbij : Function.Bijective
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact MvPolynomial.C_injective _ _ this
    · rintro ⟨p, hp⟩
      rw [MvPolynomial.mem_homogeneousSubmodule] at hp
      have ht : p.totalDegree = 0 := Nat.le_zero.mp hp.totalDegree_le
      refine ⟨MvPolynomial.coeff 0 p, Subtype.ext ?_⟩
      exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp ht).symm
  haveI : IsIso (CommRingCat.ofHom
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  unfold PSpace.str
  infer_instance

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CommonModel

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (hs : IsProjOver s) : IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := isProper_str R N
  infer_instance

end GlobalTheory.CommonModel
