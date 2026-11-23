module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

@[expose] public section

section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incV_add {k : ℕ} (x y : Fin k → E) :
    GlobalTheory.ThK.incV F (x + y) = GlobalTheory.ThK.incV F x + GlobalTheory.ThK.incV F y := by
  funext i
  simp [GlobalTheory.ThK.incV, map_add (f := _)]

theorem incV_zero {k : ℕ} : GlobalTheory.ThK.incV F (0 : Fin k → E) = 0 := by
  funext i
  simp [GlobalTheory.ThK.incV]

theorem incV_neg {k : ℕ} (x : Fin k → E) : GlobalTheory.ThK.incV F (-x) = -GlobalTheory.ThK.incV F x := by
  funext i
  simp [GlobalTheory.ThK.incV, map_neg]

theorem mem_ratVec {k : ℕ} {v : Fin k → AE F E} :
    v ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)) ↔ ∃ x, GlobalTheory.ThK.incV F x = v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, incV_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, incV_add X Z⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, incV_neg X⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩

theorem ratVec_cocompact (k : ℕ) : ∃ K : Set (Fin k → AE F E), IsCompact K ∧
    ∀ v, ∃ γ ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)), γ + v ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi fun _ => C, isCompact_univ_pi fun _ => hC, fun v => ?_⟩
  choose X hX using fun i => hCx (v i)
  exact ⟨GlobalTheory.ThK.incV F X, mem_ratVec.2 ⟨X, rfl⟩, fun i _ => hX i⟩

theorem ratVec_discrete (k : ℕ) :
    DiscreteTopology (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  obtain ⟨V, hV, hV0⟩ := kfour.exists_nhds_inclR (F := F) (E := E)
  have hW : (⋂ i, (fun v : Fin k → AE F E => v i) ⁻¹' V) ∈ 𝓝 (0 : Fin k → AE F E) := by
    refine Filter.iInter_mem.2 fun i => ?_
    exact (continuous_apply i).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨O, hOW, hO, h0⟩ := mem_nhds_iff.1 hW
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert hO.preimage continuous_subtype_val using 1
  ext ⟨x, hx⟩
  constructor
  · intro h
    have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
    subst h1
    exact h0
  · intro h
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hx
    have h2 : X = 0 := by
      funext i
      exact hV0 _ (Set.mem_iInter.1 (hOW h) i)
    subst h2
    exact Set.mem_singleton_iff.2 (Subtype.ext incV_zero)

theorem ratVec_countable (k : ℕ) :
    Countable (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  haveI := kfour.countable_E (E := E)
  have h : (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))) :
      Set (Fin k → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))).mono fun v hv => ?_
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hv
    exact ⟨X, rfl⟩
  exact h.to_subtype

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

def eA : AE F E := (((R.ε : ℤ) : E) : E) |> inclR (F := F) (E := E) (AF F)

def elt (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : d.G :=
  if h : ∃ x : d.G, inFrame d.b x = M then h.choose else 1

def uA (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)

def uMat (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (uA L u) 0 0 ((uA L (-u))ᵀ.map (cA σ))

def bMat (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 β 0 1

def sB (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(eA R * cA σ (b j))))

def aB (δ : E) (a : AF F) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ (a • inclR (F := F) (E := E) (AF F) δ)

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def phz (d : SD σ) (f : d.G → ℂ) (s₁ z : ℂ) (x : d.G) : ℂ := ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x

abbrev Cs (d : SD σ) : Type := GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y)

def rep {d : SD σ} (q : Cs d) : d.G := ((Quot.out q : rat2 σ d.Y) : d.G)

def LagrangianCondition {d : SD σ} (L : LD d) (γ : d.G) : Prop := ∀ i, inFrame d.b γ (Sum.inr i) (Sum.inl L.i₀) = 0

def kq {d : SD σ} (L : LD d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (T : nF σ d.Y d.b)
    (uM : (Fin L.n → AE F E) → d.G) (γ x : d.G) (p : (Fin L.n → AE F E) × nA σ d.Y d.b) : ℂ :=
  phz d f s₁ z (γ * (nb p.2 * (uM p.1 * x))) *
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * p.2.1))))

def tm {d : SD σ} (L : LD d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (γ x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (fun g => phz d f s₁ z (γ * g)) T (uM u * x) ∂ν

def sec2 {d : SD σ} (L : LD d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (x : d.G) : ℂ :=
  ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q.1) x

def first {d : SD σ} (L : LD d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → G2 σ L.Y) (lam' : Measure (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1

end PositivityTheory.SiegelWeilFormula.Act

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def Au {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne {d : SD σ} (L : LD d) (j : Fin L.n) : L.em j ≠ L.i₀ := fun h => (L.rng (L.em j)).2 ⟨j, rfl⟩ h

theorem Au_mul {d : SD σ} (L : LD d) (u v : Fin L.n → AE F E) : Au L u * Au L v = Au L (u + v) := by
  have h0 : (∑ j, Matrix.single L.i₀ (L.em j) (u j)) * (∑ k, Matrix.single L.i₀ (L.em k) (v k)) = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun k _ => Matrix.single_mul_single_of_ne _ _ _ _ (em_ne L j) _
  simp only [Au, add_mul, mul_add, one_mul, mul_one, h0, add_zero, Pi.add_apply, Matrix.single_add,
    Finset.sum_add_distrib, add_assoc]

theorem Au_zero {d : SD σ} (L : LD d) : Au L 0 = 1 := by simp [Au]

theorem cA_injective (d : SD σ) : Function.Injective (cA σ) := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  have hb : Function.Bijective σ := AlgHom.bijective σ
  exact (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective σ hb)).injective

theorem frame_blk (d : SD σ) {x : d.G} {A A' : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = Matrix.fromBlocks A 0 0 A') : Aᵀ * A'.map (cA σ) = 1 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h2 := kunf.frame_eq hε x
  rw [h] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  exact (Matrix.fromBlocks_inj.1 h2).2.1

theorem blk_unique (d : SD σ) {x y : d.G} {A A₁ A₂ : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (hx : inFrame d.b x = Matrix.fromBlocks A 0 0 A₁) (hy : inFrame d.b y = Matrix.fromBlocks A 0 0 A₂) : x = y := by
  have h1 := frame_blk d hx
  have h2 := frame_blk d hy
  have h1' : A₁.map (cA σ) * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have e : A₁.map (cA σ) = A₂.map (cA σ) := by
    calc A₁.map (cA σ) = A₁.map (cA σ) * (Aᵀ * A₂.map (cA σ)) := by rw [h2, Matrix.mul_one]
      _ = A₂.map (cA σ) := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A₁ = A₂ := Matrix.map_injective (cA_injective d) e
  apply kunf.inFrame_injective d.b
  rw [hx, hy, e2]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end
