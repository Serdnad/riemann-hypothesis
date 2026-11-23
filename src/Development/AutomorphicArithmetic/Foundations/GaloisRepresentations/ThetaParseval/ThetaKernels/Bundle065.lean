module

public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.StarMemSchA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle047
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepAd
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle053
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
namespace PositivityTheory.ThKG.Loc.Cone.Vf
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}
section Alg
variable {R A α β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype α] [Fintype β]
end Alg
theorem dbl_eigen_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} {φ} (hφ : M.IsVac B.ψ v φ)
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)} (hd' : ∀ x, d'.e xᵀ = M.co.e x)
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))}
    (hdd : IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd) {omd}
    (hsp : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd) (g : UG (cA σ) (dbl (incM F X.J)))
    (hg : At (evFin F v) (g.1.1 - 1)) (hg' : PresD v X (g⁻¹).1.1) :
    ∃ c : ℂ, Acts (evFin F v) (omd g) (boxFun φ (star φ)) (c • boxFun φ (star φ)) := by
  obtain ⟨hs, h0, θ, -, hθ⟩ := hφ
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have hv : ∀ γ ∈ latAtV X W v, schr (psiAt B.ψ v) (locCo M.co v γ) φ = _ := fun γ hγ =>
    (eq_of_acts v h₁ (h₀ φ hs) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) φ)).trans
      (eq_of_acts v h₁ (h₀ φ hs) (hθ γ hγ)).symm
  set θ' := inclR (F := F) (AF F) (θ : E)
  refine eigen dd hB.std {z | ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, z = Matrix.fromCols γ₁ᵀ γ₂ᵀ} ?_ ?_
    (fun z => B.ψ (⅟(2 : AF F) * symp (cA σ) θ' (incM F W.J) (dbl (incM F X.J)) z z)) (sb_box_loc hs (sb_star hs)) ?_ ?_
    (omd g) (hsp.pres g) (hsp.adm g) (actB (cA σ) g) (hsp.impl g) ?_ ?_
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩ u hu
    ext i (j | j)
    exacts [congrFun (congrFun (hAt _ h1 u hu) j) i, congrFun (congrFun (hAt _ h2 u hu) j) i]
  · intro z hz h
    have ez : z = Matrix.fromCols (z.toCols₁ᵀ)ᵀ (z.toCols₂ᵀ)ᵀ := (Matrix.fromCols_toCols z).symm
    refine ⟨_, _root_.PositivityTheory.ThK.Vac.mem_latAtV_k hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, _, _root_.PositivityTheory.ThK.Vac.mem_latAtV_k hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, ez⟩
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inl i)
    · have := h _ ⟨γ, hγ, 0, zero_mem _, rfl⟩
      rwa [ez, symp_dbl, symp_zero, sub_zero] at this
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inr i)
    · have := h _ ⟨0, zero_mem _, -γ, neg_mem hγ, rfl⟩
      rwa [ez, symp_dbl, symp_zero, zero_sub, ← neg_one_smul (AF F) γ, symp_smul, neg_one_mul, neg_neg] at this
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    exact fun e => mul_ne_zero hx (star_ne_zero.2 hx) (congrFun e (Sum.elim x x))
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    have e : locCo dd v (Matrix.fromCols γ₁ᵀ γ₂ᵀ) = (Sum.elim (locCo M.co v γ₁).1 (locCo M.co v γ₂).1,
        Sum.elim (locCo M.co v γ₁).2 (-(locCo M.co v γ₂).2)) := by
      have := hdd γ₁ᵀ γ₂ᵀ
      rw [hd', hd'] at this
      ext (i | i) <;> simp [locCo, this]
    have a2 : At (evFin F v) (⅟(2 : AF F) * symp (cA σ) θ' (incM F X.J) (incM F W.J) γ₂ γ₂) := fun u hu => by
      rw [smul_eq_mul, mul_left_comm, ← symp_smul, hAt _ h2 u hu, symp_zero, mul_zero]
    rw [e, schr_box hB.std, hv _ h1, hv _ h2, symp_dbl, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← star_psi hB.std a2]
    funext x
    simp only [boxFun, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  · intro u hu
    have : u * (g.1.1 - 1)ᵀ = 0 := by
      rw [← idem_smul hg, Matrix.transpose_smul, Matrix.mul_smul, ← Matrix.smul_mul]
      change (sg v 1 • u) * _ = 0
      rw [hu, Matrix.zero_mul]
    rwa [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    obtain ⟨a, ha, b, hb, c, hc, e, he, eg⟩ := hg'
    refine ⟨Matrix.fromCols γ₁ᵀ γ₂ᵀ * ((g⁻¹).1.1)ᵀ, ⟨a * γ₁ + b * γ₂, add_mem (mul_latAtV ha h1) (mul_latAtV hb h2),
      c * γ₁ + e * γ₂, add_mem (mul_latAtV hc h1) (mul_latAtV he h2), ?_⟩, ?_, ?_⟩
    · rw [eg, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_add, Matrix.transpose_mul]
    · have : g.1.1 * (g⁻¹).1.1 = 1 := g.1.mul_inv
      rw [actB, Matrix.mul_assoc, ← Matrix.transpose_mul, this, Matrix.transpose_one, Matrix.mul_one]
    · rw [symp, symp, hTens_mul (cA σ) _ (g⁻¹).2]
end PositivityTheory.ThKG.Loc.Cone.Vf
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Rat
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {η : E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
theorem mem_ratHerm_k {S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n} :
    S ∈ MeasP.ratHerm F E σ d.n ↔ ∃ M : Matrix (Fin d.n) (Fin d.n) E, incM F M = (S.1 : Mx F E d.n d.n) := by
  simp only [MeasP.ratHerm, AddSubgroup.mem_comap, AddMonoidHom.mem_range]
  rfl
def ratE_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    MeasP.ratHerm F E σ d.n ≃ nF σ d.Y d.b where
  toFun S := ⟨(_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm).symm S.1, by
    rw [mem_nF_iff]
    obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.MeasD.mem_ratHerm_k.1 S.2
    refine ⟨-(η • Mᵀ), ?_⟩
    show -(inclR (F := F) (AF F) η • ((S.1).1 : Mx F E d.n d.n)ᵀ) = _
    rw [← hM]
    ext a b
    simp [incM, Matrix.map_apply, map_mul, map_neg]⟩
  invFun γ := ⟨_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm γ.1, by
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.mem_ratHerm_k]
    obtain ⟨T, hT⟩ := (mem_nF_iff γ.1).1 γ.2
    refine ⟨-(η⁻¹ • Tᵀ), ?_⟩
    show _ = ((hOf γ.1).1 : Mx F E d.n d.n)
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, hT]
    ext a b
    simp [incM, Matrix.map_apply, map_mul, map_neg]⟩
  left_inv S := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm).apply_symm_apply S.1)
  right_inv γ := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm).symm_apply_apply γ.1)
end Rat
theorem meas_hOf_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    MeasurableEmbedding hOf ∧ (lam.map hOf).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (MeasP.ratHerm F E σ d.n) (hOf '' 𝓖) (lam.map hOf) ∧ lam.map hOf (hOf '' 𝓖) = 1 := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨-, -, -, hbo⟩ := nA_top hσ d.ok.frame
  haveI := hbo
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) := ⟨rfl⟩
  obtain ⟨-, hlam, hfd, h1⟩ := hc
  letI hLamHaar : lam.IsAddHaarMeasure := hlam
  let e := _root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hR.ne hR.hof hR.herm
  let eM := e.toHomeomorph.toMeasurableEquiv
  have hemb : MeasurableEmbedding hOf := eM.measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact e.toAddEquiv.isAddHaarMeasure_map lam e.continuous e.symm.continuous
  · refine hfd.image_of_equiv eM.toEquiv (eM.measurePreserving_symm lam).quasiMeasurePreserving
      (_root_.PositivityTheory.SiegelWeilFormula.MeasD.ratE_k hR.ne hR.hof hR.herm) ?_
    intro S β
    show e (e.symm S.1 + β) = S.1 + e β
    rw [map_add (f := _), ContinuousAddEquiv.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
    exact h1
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def th_k (T : nF σ d.Y d.b) (β : nA σ d.Y d.b) : ℂ := d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
def th'_k (T' : nF σ L.Y L.b) (β : nA σ L.Y L.b) : ℂ :=
  d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1))))
theorem second_orbit_section_integral {f : d.G → ℂ} {s₁ z : ℂ} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)} {T : nF σ d.Y d.b}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x =
        ∫ p, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) ∧
      ∫⁻ p, ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ
        ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) < ⊤ := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  let g : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} → (Fin L.n → AE F E) × nA σ d.Y d.b → ℂ :=
    fun q => _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
  have hgi : ∀ q, Integrable (g q) μ := fun q => hi q.1
  have hgs : Summable fun q => ∫ p, ‖g q p‖ ∂μ := hs.subtype _
  have htm : ∀ q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x = ∫ p, g q p ∂μ := by
    intro q
    rw [hμ, integral_prod _ (hgi q)]
    rfl
  constructor
  · unfold _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection
    simp_rw [htm]
    rw [(hasSum_integral_of_summable_integral_norm hgi hgs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [g, _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k]
    rw [tsum_mul_right]
  · have hm : ∀ q, AEMeasurable (fun p => ‖g q p‖ₑ) μ := fun q => (hgi q).aemeasurable.enorm
    have e1 : ∫⁻ p, ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂μ =
        ∑' q, ENNReal.ofReal (∫ p, ‖g q p‖ ∂μ) := by
      rw [show (fun p => ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)},
          ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ) = fun p => ∑' q, ‖g q p‖ₑ from rfl,
        lintegral_tsum hm]
      exact tsum_congr fun q => (ofReal_integral_norm_eq_lintegral_enorm (hgi q)).symm
    rw [e1, ← ENNReal.ofReal_tsum_of_nonneg (fun q => integral_nonneg fun p => norm_nonneg _) hgs]
    exact ENNReal.ofReal_lt_top
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
