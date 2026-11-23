module

public import Development.EtaleCohomology.DivisorCycles.Bundle002
public import Development.EtaleCohomology.DivisorCycles.Bundle003
public import Development.EtaleCohomology.DivisorCycles.ConjugateIdempotents
public import Development.EtaleCohomology.DivisorCycles.CycleCount2
public import Development.EtaleCohomology.DivisorCycles.Bundle001
public import Development.EtaleCohomology.DivisorCycles.Bundle007
public import Development.EtaleCohomology.DivisorCycles.Bundle005
public import Development.EtaleCohomology.DivisorCycles.Bundle006
public import Development.EtaleCohomology.DivisorCycles.Bundle004
public import Development.EtaleCohomology.DivisorCycles.TorusPtPf
public import Development.EtaleCohomology.DivisorCycles.UnitFactorizationTheorem
public import Development.EtaleCohomology.DivisorCycles.Bundle008
public import Development.EtaleCohomology.DivisorCycles.FinPolyPf
public import Development.EtaleCohomology.DivisorCycles.MinCongr
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

namespace LateralTheory.Fin.DegAll
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_rep_image_degree_bound_all_holds_assembled : LateralTheory.DivDb.DegAll := by
  apply LateralTheory.DivDb.DegAll_of <;> first | exact etale_degree_polynomial_bound
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DegAll := etale_rep_image_degree_bound_all_holds_assembled
end LateralTheory.Fin.DegAll
end

section

namespace LateralTheory.Fin.DenseAlg
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
theorem etale_rep_dense_algebraic_hull_holds_assembled : LateralTheory.DivDb.DenseAlg := by
  apply LateralTheory.DivDb.DenseAlg₂.DenseAlg_of <;> first | exact etale_divisibility_chain_of_key | exact etale_frobenius_charpoly_separable
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DenseAlg := etale_rep_dense_algebraic_hull_holds_assembled
end LateralTheory.Fin.DenseAlg
end

section

namespace LateralTheory.Fin.FinDense
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_open_coset_condition_holds_assembled : LateralTheory.DivDb.OpenCoset := by
  apply LateralTheory.DivDb.OpenCoset_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_finite_image_dense_holds_assembled : LateralTheory.DivDb.FinDense := by
  apply LateralTheory.DivDb.FinDense_of <;> first | exact etale_frobenius_charpoly_separable | exact etale_open_coset_condition_holds_assembled
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinDense := etale_finite_image_dense_holds_assembled
end LateralTheory.Fin.FinDense
end

section

namespace LateralTheory.Fin.Key
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem etale_idempotent_conjugacy_of_key : LateralTheory.DivDb.IdemConj := by
  apply LateralTheory.DivDb.ConjugateIdempotents.IdemConj_of <;> first | exact etale_matrix_units_system_of_key
theorem etale_unit_factorization_of_key : LateralTheory.DivDb.UnitFactorization := by
  apply LateralTheory.DivDb.UnitFactorizationTheorem.UnitFactor_of
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_zariski_closure_mul_closed_of_key : LateralTheory.DivDb.ZclMul := by
  apply LateralTheory.DivDb.ZclMul_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_tangent_index_divides_of_key : LateralTheory.DivDb.TanIndex := by
  apply LateralTheory.DivDb.TangentIndexDvd.TanIndex_of <;> first | exact etale_divisibility_chain_of_key | exact etale_zariski_closure_mul_closed_of_key
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_unipotent_part_trivial_of_key : LateralTheory.DivDb.Unip := by
  apply LateralTheory.DivDb.UnipotentPartTrivial.Unip_of <;> first | exact etale_exponent_vanishing_of_key
theorem etale_generic_spectrum_of_key : LateralTheory.DivDb.GenSpec := by
  apply LateralTheory.DivDb.GenSpecProof.GenSpec_of
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_torus_point_exists_of_key : LateralTheory.DivDb.TorusPt := by
  apply LateralTheory.DivDb.TorusPtPf.TorusPt_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_special_point_exists_of_key
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCount₂.CycleCount_of
theorem etale_divisibility_key_criterion_of_components : LateralTheory.DivDb.Key := by
  apply LateralTheory.DivDb.KeyPf.Key_of <;> first | exact etale_idempotent_conjugacy_of_key | exact etale_matrix_units_system_of_key | exact etale_unit_factorization_of_key | exact etale_tangent_index_divides_of_key | exact etale_unipotent_part_trivial_of_key | exact etale_zariski_closure_mul_closed_of_key | exact etale_generic_spectrum_of_key | exact etale_torus_point_exists_of_key | exact etale_tangent_degree_bound_of_key | exact etale_cycle_count_eigenvalues_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Key := etale_divisibility_key_criterion_of_components
end LateralTheory.Fin.Key
end

section

namespace LateralTheory.Fin.Semis
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Semis := etale_semisimplicity_instance
end LateralTheory.Fin.Semis
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

theorem goal_of (hSpec : SpecLie) (hDeg : DegAll) (hStruct : Struct) (hKey : Key) (hBig : BigCorner)
    (hSemis : Semis) (hMU : MatrixUnits₂) (hRep : Rep) (hDA : DenseAlg) (hSub : FinSub) (hFD : FinDense)
    (hFP : FinPoly) (hEm : FinEmbed) : DivWCoreLac := by
  intro Γ _ _ _ _ K K' _ _ _ _ _ _ _ _ _ N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  obtain ⟨r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, k, T, T', hT, -, hs⟩ :=
    plus_of hSpec hDeg hStruct hKey hBig hSemis hMU hRep hDA hSub hFD hFP hEm
      Γ K K' N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  refine ⟨r, h1, h2, h3, ⟨k, Matrix.of fun q a => T q.2 q.1 a, ?_, fun g => ?_⟩, h4, h5, h6, h7, h8, h9, h10⟩
  · have hC : (Matrix.of fun a (q : Fin n × Fin k) => T' q.2 a q.1) *
        (Matrix.of fun (q : Fin n × Fin k) a => T q.2 q.1 a) = 1 := by
      rw [← hs]; ext a b
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply, Fintype.sum_prod_type_right]
    refine le_antisymm ((Matrix.rank_le_card_width _).trans (by simp)) ?_
    have := Matrix.rank_mul_le_right (Matrix.of fun a (q : Fin n × Fin k) => T' q.2 a q.1)
      (Matrix.of fun (q : Fin n × Fin k) a => T q.2 q.1 a)
    rw [hC] at this
    simpa using this
  · ext ⟨i, j⟩ a
    have := congrFun (congrFun (hT j g) i) a
    simp only [Matrix.mul_apply] at this
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, this]

end LateralTheory.DivDb
end

section

namespace LateralTheory.Fin.FinEmbed
theorem etale_semisimple_finite_embedding_holds_assembled : LateralTheory.DivDb.FinEmbed := by
  apply LateralTheory.DivDb.FinEmbedPf.FinEmbed_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinEmbed := etale_semisimple_finite_embedding_holds_assembled
end LateralTheory.Fin.FinEmbed
end

section

namespace LateralTheory.Fin.FinSub
theorem finite_subrepresentation_etale_charpoly_instance : LateralTheory.DivDb.FinSub := by
  apply LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinSub := finite_subrepresentation_etale_charpoly_instance
end LateralTheory.Fin.FinSub
end

section

namespace LateralTheory.Fin.MatrixUnits₂
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.MatrixUnits₂ := etale_matrix_units_system_of_key
end LateralTheory.Fin.MatrixUnits₂
end

section

namespace LateralTheory.Fin.BigCorner
theorem etale_big_corner_statement_holds_assembled : LateralTheory.DivDb.BigCorner := by
  apply LateralTheory.DivDb.BigCorner₂.BigCorner_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.BigCorner := etale_big_corner_statement_holds_assembled
end LateralTheory.Fin.BigCorner
end

section

namespace LateralTheory.Fin.FinPoly
theorem charpoly_eq_of_annihilating_poly_etale_instance : LateralTheory.DivDb.FinPoly := by
  apply LateralTheory.DivDb.FinPolyPf.FinPoly_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinPoly := charpoly_eq_of_annihilating_poly_etale_instance
end LateralTheory.Fin.FinPoly
end

section

namespace LateralTheory.Fin.Rep
theorem etale_representation_realization_instance : LateralTheory.DivDb.Rep := by
  apply LateralTheory.DivDb.RepPf.Rep_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Rep := etale_representation_realization_instance
end LateralTheory.Fin.Rep
end
