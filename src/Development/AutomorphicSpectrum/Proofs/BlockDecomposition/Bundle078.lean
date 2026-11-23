module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle047
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.RgEisTop

section Units

variable {M : Type} [TopologicalSpace M] [Monoid M] [ContinuousMul M] [T2Space M]

theorem isClosedEmbedding_embedProduct : IsClosedEmbedding (Units.embedProduct M) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hr : Set.range (Units.embedProduct M) =
      {p : M × Mᵐᵒᵖ | p.1 * MulOpposite.unop p.2 = 1} ∩
        {p : M × Mᵐᵒᵖ | MulOpposite.unop p.2 * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, hu⟩
      have h1 : (u : M) = x := congrArg Prod.fst hu
      have h2 : MulOpposite.op ((u⁻¹ : Mˣ) : M) = y := congrArg Prod.snd hu
      subst h1 h2
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, MulOpposite.unop y, h1, h2⟩, rfl⟩
  rw [hr]
  have hu : Continuous fun p : M × Mᵐᵒᵖ => MulOpposite.unop p.2 :=
    MulOpposite.continuous_unop.comp continuous_snd
  exact (isClosed_eq (continuous_fst.mul hu) continuous_const).inter
    (isClosed_eq (hu.mul continuous_fst) continuous_const)

end Units

section Mat

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem generalLinear_t2Space [T2Space R] : T2Space (GL ι R) :=
  (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.t2Space

theorem gl_locallyCompact [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL ι R) := by
  have : LocallyCompactSpace (Matrix ι ι R) := inferInstanceAs (LocallyCompactSpace (ι → ι → R))
  have : LocallyCompactSpace (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isClosedEmbedding.locallyCompactSpace
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).locallyCompactSpace

theorem gl_secondCountable [T2Space R] [SecondCountableTopology R] :
    SecondCountableTopology (GL ι R) := by
  have : SecondCountableTopology (Matrix ι ι R) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → R))
  have : SecondCountableTopology (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isEmbedding.secondCountableTopology
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.secondCountableTopology

end Mat

open PositivityTheory.RgEis

theorem isClosed_uSub {E R : Type} [Field E] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (A : Ad E R) (hσ : Continuous A.σ) (ε : ℤˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    IsClosed (A.uSub ε ι : Set (GL (ι ⊕ ι) R)) := by
  have hv : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    Units.continuous_val
  have hm : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ :=
    hv.matrix_map hσ
  exact isClosed_eq ((hv.matrix_transpose.mul continuous_const).mul hm) continuous_const

theorem grpTop : PositivityTheory.RgEis.GrpTop := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ ε
  have hc := isClosed_uSub A hA.σcont ε ι
  have hce : IsClosedEmbedding (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) :=
    hc.isClosedEmbedding_subtypeVal
  have := generalLinear_t2Space R (ι ⊕ ι)
  have := gl_locallyCompact R (ι ⊕ ι)
  have := gl_secondCountable R (ι ⊕ ι)
  refine ⟨generalLinear_t2Space R ι, gl_locallyCompact R ι, gl_secondCountable R ι, hce.isEmbedding.t2Space,
    hce.locallyCompactSpace, hce.isEmbedding.secondCountableTopology, ?_⟩
  exact hce.isCompact_preimage (hA.toGoodL.kcpt (ι ⊕ ι))

end GlobalTheory.CompanionTheory.RgEisTop
end

section

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

section Heights

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isHt_mono {Γ K P P' : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) (hP : P' ≤ P) : IsHt Γ K P' η :=
  ⟨fun p hp g => h.left p (hP hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hP hp), h.cont⟩

theorem isHt_lin {Γ K P : Subgroup G} {η θ : G → ℝ} (x y : ℝ) (h₁ : IsHt Γ K P η) (h₂ : IsHt Γ K P θ) :
    IsHt Γ K P fun g => x * η g + y * θ g := by
  refine ⟨?_, ?_, ?_, (continuous_const.mul h₁.cont).add (continuous_const.mul h₂.cont)⟩
  · intro p hp g
    simp only [h₁.left p hp g, h₂.left p hp g]
    ring
  · intro g k hk
    simp only [h₁.right g k hk, h₂.right g k hk]
  · intro γ hγ hp
    simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp, mul_zero, add_zero]

theorem isHt_congr {Γ K P : Subgroup G} {η θ : G → ℝ} (h : IsHt Γ K P η) (e : ∀ g, θ g = η g) : IsHt Γ K P θ := by
  rwa [show θ = η from funext e]

theorem conv_congr {Γ P : Subgroup G} {l l' : G → ℝ} (h : Conv Γ P l) (e : ∀ g, l' g = l g) : Conv Γ P l' := by
  rwa [show l' = l from funext e]

end Heights

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]


open scoped Classical in
theorem wallQ (hTr : Transfer) (hTop : GrpTop) (hPar : ParLaw) (hLQ : LeviQ) (A : Ad E R) (hA : A.Good) (ε : ℤˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Set ι) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι))
    (hSg : A.Sg ε (sᶜ : Set ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasWall (A.uΓ ε ι ⊓ A.uQ ε s) (A.uK ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uC ε ι)
      (fun g => A.uH ε Set.univ g - A.uH ε s g) (fun g => A.uH ε Set.univ g - A.uH ε s g)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g)) ρ := by
  obtain ⟨π, j, c₀, hL, hP, hIw, hPH⟩ := hLQ E R A hA ι ε s hI
  obtain ⟨-, -, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨-, -, -, u₄, u₅, -, u₇⟩ := hTop E R A hA (sᶜ : Set ι) ε
  have hP' := (hPar E R A hA (sᶜ : Set ι) ε Set.univ).2 (by rwa [inf_idem])
  rw [inf_idem] at hP'
  obtain ⟨hp, hh, -⟩ := hP'
  have hβ' : IsHt (A.uΓ ε (sᶜ : Set ι)) (A.uK ε (sᶜ : Set ι)) (A.uQ ε Set.univ)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card (sᶜ : Set ι) : ℝ) 0 hh hh) fun g => by ring
  have hPβ : PullHt (A.uK ε ι) (A.uQ ε s) π
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g))
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) := by
    intro q k hk
    have := hPH q k hk
    simp only at this ⊢
    rw [this]
  exact (hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j c₀ _ _ _ _ _ _ _ _ _ _ 0 u₇ hL hP hP hP hp hp hp hh hh hβ'
    hPH hPH hPβ hPH).1 (hSg hIw)

theorem wallsS (hTr : Transfer) (hTw : Twist) (hTop : GrpTop) (hPar : ParLaw) (hLS : LeviS) (A : Ad E R) (hA : A.Good)
    (hMir : A.MirGL) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι) (hN : 2 ≤ Fintype.card ι)
    (hS : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasFirst (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)) ρ ∧
    HasWall (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uC ε ι) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g) (A.uH ε {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g) ρ ∧
    HasLast (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (A.uH ε Set.univ) (Fintype.card ι) ρ := by
  obtain ⟨π, j, hL, hP, -, hH⟩ := hLS E R A hA ι ε hS
  obtain ⟨g₁, g₂, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  have hk := hA.kcpt ι
  obtain ⟨a₁, a₂, ch, h₀, -⟩ := (hPar E R A hA ι ε {i₀}).1
  obtain ⟨b₁, b₂, -, h₁, -⟩ := (hPar E R A hA ι ε {i₁}ᶜ).1
  obtain ⟨u₁, u₂, -, hu, hst⟩ := (hPar E R A hA ι ε Set.univ).1
  rw [hst] at u₁ u₂ hu
  have hPS : IsPull (A.uQ ε Set.univ) (A.uQ ε Set.univ) ⊤ π 1 (A.uC ε ι) (A.cGL ι) := by
    have := hP Set.univ
    rwa [inf_idem, hst] at this
  have e : (1 : GL ι R → ℂ) * A.cGL ι = A.cGL ι := one_mul _
  obtain ⟨m₁, m₂, m₃⟩ := hMir ι i₀ i₁ hN
  have d₁ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin 1 (-1) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₂ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ)
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (1 - (Fintype.card ι : ℝ)) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₃ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (-1) h₀ (isHt_mono hu le_top)) fun g => by ring
  have p₁ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₂ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₃ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g)
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₀} q k hk', hH Set.univ q k hk']
  have T₁ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₀}) (stab R {i₁}ᶜ) 1 (A.cGL ι) (A.htGL {i₀})
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g)
    (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ a₁ b₁
  have T₂ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₁}ᶜ) (stab R {i₀}) 1 (A.cGL ι)
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
    (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ b₁ a₁
  rw [e] at T₁ T₂
  have X₁ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₀}) (hP {i₁}ᶜ) u₂ a₂ b₂ h₀ d₁ d₂ (hH {i₀}) p₁ p₂ (hH Set.univ)
  have X₂ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₁}ᶜ) (hP {i₀}) u₂ b₂ a₂ d₁ h₀ d₃ p₁ (hH {i₀}) p₃ (hH Set.univ)
  exact ⟨X₁.2.1 (T₁.2.1 m₁), X₂.1 (T₂.1 m₂), X₁.2.2 (T₁.2.2 m₃)⟩


open Classical in
theorem sgStep : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := by
  classical
  intro hGal hTr hTw hTop hPar hLS hLQ hCG hCU E R _ _ _ _ _ _ _ A hA hMir ε ι _ _ hN hIH hS W _ _ _ ρ hρ
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨π, j, -, -, hIw, -⟩ := hLS E R A hA ι ε hS
  obtain ⟨-, -, -, t₄, t₅, t₆, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨Ra, ca₁, ca₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀} (hIw _)
  obtain ⟨Rb, -, cb₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀}ᶜ (hIw _)
  have pS := (hPar E R A hA ι ε Set.univ).2 (hIw _)
  rw [inf_idem] at pS
  have pA := (hPar E R A hA ι ε {i₀}).2 (hIw _)
  have pB := (hPar E R A hA ι ε {i₀}ᶜ).2 (hIw _)
  have hc₀ : ∀ f : Fintype ({i₀}ᶜ : Set ι), @Fintype.card _ f = Fintype.card ι - 1 := fun f => by
    rw [Fintype.card_compl_set]; simp
  have hc₁ : ∀ f : Fintype (({i₀}ᶜ : Set ι)ᶜ : Set ι), @Fintype.card _ f = 1 := fun f => by
    rw [Fintype.card_compl_set, hc₀]; omega
  have hc₀' : ∀ f : Fintype ({i₀}ᶜ : Set ι), ((@Fintype.card _ f : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := fun f => by
    rw [hc₀, Nat.cast_sub (by omega)]; simp
  have hq := fun (s : Set ι) (f : Fintype (sᶜ : Set ι)) (d : DecidableEq (sᶜ : Set ι)) => @hIH (sᶜ : Set ι) f d
  have w₁ := wallQ hTr hTop hPar hLQ A hA ε {i₀} (hIw _)
    (hq _ _ _ (by rw [hc₀]; omega) (by rw [hc₀]; omega)) ρ hρ
  have w₂ := wallQ hTr hTop hPar hLQ A hA ε {i₀}ᶜ (hIw _)
    (hq _ _ _ (hc₁ _).ge (by rw [hc₁]; omega)) ρ hρ
  rw [hc₀'] at w₁
  rw [hc₁] at w₂
  simp only [Nat.cast_one, one_mul] at w₂
  rw [show (fun g => A.uH ε Set.univ g - A.uH ε {i₀}ᶜ g) = fun g => -(A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) from
    funext fun g => by ring] at w₂
  obtain ⟨s₁, s₂, s₃⟩ := wallsS hTr hTw hTop hPar hLS A hA hMir ε i₀ i₀ hN hS ρ hρ
  refine hGal (A.U ε ι) W (A.uK ε ι) ρ t₇ hρ inferInstance (A.uΓ ε ι) (A.uQ ε Set.univ)
    (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}) (A.uQ ε {i₀}ᶜ) (A.uC ε ι)
    (A.uH ε Set.univ) (A.uH ε {i₀}) (fun g => A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) (Fintype.card ι)
    inf_le_right inf_le_right inf_le_left inf_le_left pS.1 pA.1 pB.1 pS.2.1 pA.2.1
    (isHt_congr pB.2.1 fun g => by ring) ⟨max Ra Rb, fun y hy => ca₁ y (lt_of_le_of_lt (le_max_left _ _) hy),
      fun z y hz hy => ca₂ z y (lt_of_le_of_lt (le_max_left _ _) hz) (lt_of_le_of_lt (le_max_left _ _) hy),
      fun r y hr hy => conv_congr (cb₂ r y (lt_of_le_of_lt (le_max_right _ _) hr)
        (lt_of_le_of_lt (le_max_right _ _) hy)) fun g => by ring⟩ s₁ w₂ s₂ w₁ s₃

end GlobalTheory.CompanionTheory.RgEis
end
end

section

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisScale

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

lemma ht_rep {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (q : Cos P Γ) (g : G) :
    l (rep q * g) = l g := by
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [hl.left _ (Subgroup.mem_top _), hl.rat _ hq (Subgroup.mem_top _), zero_add]

lemma eis_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (c : G → ℂ)
    (ρ : K →* (W →L[ℂ] W)) (Λ Λ' : G → ℂ) (t : ℂ) (h : ∀ x, Λ' x = Λ x + t * l x) (g : G) (w : W) :
    eis Γ K P c ρ Λ' g w = Complex.exp (t * l g) • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [h, ht_rep hl, Complex.exp_add, smul_smul, mul_comm]

lemma conv_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {f f' : G → ℝ} (t : ℝ)
    (h : ∀ x, f' x = f x + t * l x) (hc : Conv Γ P f) : Conv Γ P f' := by
  intro g
  refine ((hc g).mul_right (Real.exp (t * l g))).congr fun q => ?_
  rw [h, ht_rep hl, Real.exp_add]

theorem wall_scale [IsTopologicalGroup G] {K Γ P P' : Subgroup G} {ρ : K →* (W →L[ℂ] W)} {c : G → ℂ}
    {η η' β l : G → ℝ} {s : ℝ} (hs : 0 < s) (hl : IsHt Γ K ⊤ l) {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (secSp K P c ρ →L[ℂ] secSp K P' c ρ)} {H : ℂ → G → (secSp K P c ρ →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H) :
    Wall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ (secSp K P c ρ) (R / s)
      (fun z => D (s * z)) (fun z => Op (s * z))
      (fun z g => Complex.exp (s * z * l g) • H (s * z) g) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hre : ∀ z : ℂ, ((s : ℂ) * z).re = s * z.re := fun z => by simp
  have hσ : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hgtx : ∀ x : ℝ, R / s < x → R < s * x := fun x hx => by
    rwa [div_lt_iff₀' hs] at hx
  have hltx : ∀ x : ℝ, x < -(R / s) → s * x < -R := fun x hx => by
    have h1 := mul_lt_mul_of_pos_left hx hs
    have h2 : s * -(R / s) = -R := by field_simp
    linarith
  have hlec : ∀ {x : ℝ} {z : ℂ}, x ≤ z.re → s * x ≤ ((s : ℂ) * z).re := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlec' : ∀ {y : ℝ} {z : ℂ}, z.re ≤ y → ((s : ℂ) * z).re ≤ s * y := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlc : Continuous fun g => (l g : ℂ) := Complex.continuous_ofReal.comp hl.cont
  refine
    { le := hw.le
      pos := div_nonneg hw.pos hs.le
      convR := fun x hx => ?_
      convL := fun x hx => ?_
      dEnt := ⟨hw.dEnt.1.comp hσ, fun b a => ?_⟩
      dNe := ?_
      op := ⟨?_, fun b a ha => ?_⟩
      hol := fun g => ?_
      cont := ?_
      bdd := fun b a g => ?_
      eqR := fun z hz g w => ?_
      eqL := fun z hz g w => ?_ }
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convR (s * x) (hgtx x hx))
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convL (s * x) (hltx x hx))
  · obtain ⟨M, hM⟩ := hw.dEnt.2 (s * b) (s * a)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · obtain ⟨z, hz⟩ := hw.dNe
    refine ⟨z / s, ?_⟩
    have : (s : ℂ) * (z / s) = z := by field_simp
    simpa [this] using hz
  · refine hw.op.1.comp hσ.differentiableOn fun z hz => ?_
    have hz' : z.re < -(R / s) := hz
    show ((s : ℂ) * z).re < -R
    rw [hre]; exact hltx _ hz'
  · obtain ⟨M, hM⟩ := hw.op.2 (s * b) (s * a) (hltx a ha)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · have h1 : Differentiable ℂ fun z : ℂ => Complex.exp (s * z * l g) := by fun_prop
    exact h1.smul ((hw.hol g).comp hσ)
  · have h1 : Continuous fun y : ℂ × G => Complex.exp (s * y.1 * l y.2) :=
      ((continuous_const.mul continuous_fst).mul (hlc.comp continuous_snd)).cexp
    have h2 : Continuous fun y : ℂ × G => H (s * y.1) y.2 :=
      hw.cont.comp (f := fun y : ℂ × G => ((s : ℂ) * y.1, y.2)) (by fun_prop)
    exact h1.smul h2
  · obtain ⟨U, hU, M, hM⟩ := hw.bdd (s * b) (s * a) g
    have hV : {g' | |l g'| < |l g| + 1} ∈ 𝓝 g :=
      (isOpen_lt (continuous_abs.comp hl.cont) continuous_const).mem_nhds (by simp)
    refine ⟨U ∩ {g' | |l g'| < |l g| + 1}, inter_mem hU hV,
      Real.exp (s * max |b| |a| * (|l g| + 1)) * M, fun z h1 h2 g' hg' => ?_⟩
    have hH := hM _ (hlec h1) (hlec' h2) g' hg'.1
    have hg2 : |l g'| < |l g| + 1 := hg'.2
    have hz : |z.re| ≤ max |b| |a| := abs_le_max_abs_abs h1 h2
    have hE : ‖Complex.exp (s * z * l g')‖ ≤ Real.exp (s * max |b| |a| * (|l g| + 1)) := by
      rw [Complex.norm_exp, Complex.re_mul_ofReal, hre]
      apply Real.exp_le_exp.mpr
      calc s * z.re * l g' ≤ |s * z.re * l g'| := le_abs_self _
        _ = s * |z.re| * |l g'| := by rw [abs_mul, abs_mul, abs_of_pos hs]
        _ ≤ s * max |b| |a| * (|l g| + 1) := by gcongr
    rw [norm_smul]
    exact mul_le_mul hE hH (norm_nonneg _) (Real.exp_pos _).le
  · rw [eis_twist hl c ρ (fun x => s * z * η x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqR _ (by rw [hre]; exact hgtx _ hz) g w, smul_comm]
  · rw [eis_twist hl c ρ (fun x => β x - s * z * η' x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqL _ (by rw [hre]; exact hltx _ hz) g w]

theorem scale : PositivityTheory.RgEis.Scale := by
  intro G _ _ _ _ _ W _ _ _ K ρ _ _ Γ P P' c η η' β l s hs hl hW
  obtain ⟨R, D, Op, H, hw⟩ := hW
  exact ⟨_, _, _, _, wall_scale hs hl hw⟩

end GlobalTheory.CompanionTheory.RgEisScale
end
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.section_invariance_coset_sum : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.stage_eis | exact GlobalTheory.CompanionTheory.RgEisCross.stage_eis | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.stage_eis <;> assumption)
end

section


theorem _root_.GlobalTheory.T.section_law_holds : PositivityTheory.RgEis.SecLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSec.secLaw | exact GlobalTheory.CompanionTheory.RgEisSec.secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisSec.secLaw <;> assumption)
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.partial_fraction_coefficient_signs : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧ ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  first | exact @GlobalTheory.CompanionTheory.RgHeSign.pfSign | exact GlobalTheory.CompanionTheory.RgHeSign.pfSign | (intros; apply GlobalTheory.CompanionTheory.RgHeSign.pfSign <;> assumption)
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.partial_fraction_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, d i - pfX d d' + ∑ j, pfR d d' j / (d i - d' j) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.Frame.pfZero | exact GlobalTheory.CompanionTheory.RgHe.Frame.pfZero | (intros; apply GlobalTheory.CompanionTheory.RgHe.Frame.pfZero <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.TwistedCent

open PositivityTheory.Rg.Tf.Loc

theorem mem_twCent_twConj_iff {G : Type} [Group G] (θ : Monoid.End G) (g δ x : G) :
    x ∈ twCent θ (twConj θ g δ) ↔ g * x * g⁻¹ ∈ twCent θ δ := by
  rw [mem_twCent, mem_twCent]
  simp only [twConj, map_mul, map_inv]
  constructor
  · intro h
    calc (g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)
        = g * (x⁻¹ * (g⁻¹ * δ * θ g) * θ x) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g) * (θ g)⁻¹ := by rw [h]
      _ = δ := by group
  · intro h
    calc x⁻¹ * (g⁻¹ * δ * θ g) * θ x
        = g⁻¹ * ((g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by group
      _ = g⁻¹ * δ * θ g := by rw [h]

theorem h3 : PositivityTheory.Rg.Tf.Loc.H3 := fun _ _ θ g δ x => mem_twCent_twConj_iff θ g δ x

end GlobalTheory.CompanionTheory.TwistedCent
end
