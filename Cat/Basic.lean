namespace CT

class Quiver.{u, v} (C : Type u) where
  arrow : C → C → Type v
infixr:200 " ⟶ " => Quiver.arrow

class CatIdMorphism.{u, v} (C : Type u) (arrow : C → C → Type v) where
  id : (x : C) → arrow x x
prefix:210 "𝟙 " => CatIdMorphism.id

class CatComp.{u, v} (C : Type u) (arrow : C → C → Type v) where
  comp {X Y Z : C} : arrow X Y → arrow Y Z → arrow X Z
infixr:180 " ≫ " => CatComp.comp

class Category.{u, v} (C : Type u) extends
      Quiver.{u, v} C,
      CatIdMorphism.{u, v} C toQuiver.arrow,
      CatComp.{u, v} C toQuiver.arrow
    where
  id_comp : ∀ {x y : C} (f : x ⟶ y), 𝟙 x ≫ f = f
  comp_id : ∀ {x y : C} (f : x ⟶ y), f ≫ 𝟙 y = f
  assoc : ∀ {w x y z : C} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z),
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

attribute [simp] Category.id_comp Category.comp_id

@[ext]
structure Functor
    (C : Type u) (D : Type u')
    [Category.{u, v} C] [Category.{u', v'} D] : Type max u u' v v' where
  omap : C → D
  fmap : ∀ {x y : C}, (x ⟶ y) → (omap x ⟶ omap y)
  map_id : ∀ X : C, fmap (𝟙 X) = 𝟙 (omap X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), fmap (f ≫ g) = fmap f ≫ fmap g

def Functor.id (C : Type u) [Category C] : Functor C C where
  omap := _root_.id
  fmap := _root_.id
  map_id := by simp
  map_comp := by simp

def Functor.comp [Category C] [Category D] [Category E]
    (F : Functor C D) (G : Functor D E) : Functor C E where
  omap := G.omap ∘ F.omap
  fmap := G.fmap ∘ F.fmap
  map_id X := by simp [F.map_id, G.map_id]
  map_comp f g := by simp [F.map_comp, G.map_comp]

infix:200 " ⥤ " => Functor
infix:180 " ⋙ " => Functor.comp

instance [Category C] [Category D] : CoeFun (C ⥤ D) (fun _ => C → D) where
  coe x := x.omap

structure NatTrans.{u1, u2} [Category.{u1, v1} C] [Category.{u2, v2} D] (F G : Functor.{u1, u2, v1, v2} C D) where
  component : ∀ X : C, F X ⟶ G X
  naturality : ∀ {X Y : C} (f : X ⟶ Y),
    F.fmap f ≫ component Y = component X ≫ G.fmap f

@[simp, reducible]
def NatTrans.id [Category C] [Category D] (F : C ⥤ D) : NatTrans F F where
  component X := 𝟙 (F.omap X)
  naturality {X Y} f := by simp

@[simp, reducible]
def NatTrans.comp [Category C] [Category D] {F G H : C ⥤ D}
    (t1 : NatTrans F G) (t2 : NatTrans G H) :
    NatTrans F H where
  component X := t1.component X ≫ t2.component X
  naturality {X Y} f := by
    repeat rw [Category.assoc]
    simp
    rw [← Category.assoc]
    rw [t1.naturality f]
    rw [Category.assoc]
    congr 1
    rw [t2.naturality f]

@[simp]
theorem NatTrans.id_comp [Category C] [Category D] {F G : C ⥤ D} (T : NatTrans F G) :
    (NatTrans.comp (NatTrans.id F) T) = T := by
  simp [NatTrans.comp, NatTrans.id]

@[simp]
theorem NatTrans.comp_id [Category C] [Category D] {F G : C ⥤ D} (T : NatTrans F G) :
    (NatTrans.comp T (NatTrans.id G)) = T := by
  simp [NatTrans.comp, NatTrans.id]

theorem NatTrans.assoc [Category C] [Category D] {E F G H : C ⥤ D}
    (t1 : NatTrans E F) (t2 : NatTrans F G) (t3 : NatTrans G H) :
    NatTrans.comp (NatTrans.comp t1 t2) t3 = NatTrans.comp t1 (NatTrans.comp t2 t3) := by
  simp [NatTrans.comp]
  ext X
  simp [Category.assoc]

instance [Category C] [Category D] : Category (C ⥤ D) where
  arrow X Y := NatTrans X Y
  id X := NatTrans.id X
  comp := NatTrans.comp
  id_comp := NatTrans.id_comp
  comp_id := NatTrans.comp_id
  assoc := NatTrans.assoc

instance {C : Type u1} {D : Type u2} [Category.{u1} C] [Category.{u2} D] :
    Category.{max u1 u2} (C × D) where
  arrow X Y := (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id X := (𝟙 X.1, 𝟙 X.2)
  comp {x y z} f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp {x y} f := by simp; congr
  comp_id {x y} f := by simp; congr
  assoc := by simp [Category.assoc]

structure Isomorphism [Category C] (X Y : C) where
  toMorphism : X ⟶ Y
  invMorphism : Y ⟶ X
  protected left_inv : toMorphism ≫ invMorphism = 𝟙 X
  protected right_inv : invMorphism ≫ toMorphism = 𝟙 Y

attribute [simp] Isomorphism.left_inv Isomorphism.right_inv

infix:150 " ≃ " => Isomorphism

def Isomorphism.of_eq [Category C] {X Y : C} : X = Y → X ≃ Y := by
  intro h
  rw [← h]
  exact ⟨𝟙 X, 𝟙 X, by simp, by simp⟩

-- instance [Category C] : CatComp C (Isomorphism) where
--   comp f g :=
--     { toMorphism := f.toMorphism ≫ g.toMorphism
--     , invMorphism := g.invMorphism ≫ f.invMorphism
--     , left_inv := by
--         conv =>
--           lhs; rw [← Category.assoc]
--           lhs; rw [Category.assoc]
--         simp
--     , right_inv := by
--         conv =>
--           lhs; rw [← Category.assoc]
--           lhs; rw [Category.assoc]
--         simp
--     }

instance [Category C] {X Y : C} : Coe (X ≃ Y) (X ⟶ Y) where
  coe x := x.toMorphism

class MonoidalCategoryStruct (C : Type u) extends Category.{u} C where
  tensor : (C × C) ⥤ C
  tensor_id : C

notation:max " 𝕀 " => MonoidalCategoryStruct.tensor_id

@[simp, reducible]
def MonoidalCategoryStruct.times_object [MonoidalCategoryStruct C] (x y : C) :=
  MonoidalCategoryStruct.tensor.omap (x, y)
@[simp, reducible]
def MonoidalCategoryStruct.times_morphism [MonoidalCategoryStruct C] {x y u v : C} (f : x ⟶ u) (g : y ⟶ v) :=
  MonoidalCategoryStruct.tensor.fmap (x := (x, y)) (y := (u, v)) (f, g)

infix:220 " ⊗ " => MonoidalCategoryStruct.times_object
infix:190 " ⨂ " => MonoidalCategoryStruct.times_morphism

class MonoidalCategory.{u,v} (C : Type u) extends MonoidalCategoryStruct.{u,v} C where
  α : ∀ (X Y Z : C), (X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)
  «λ» : ∀ X : C, 𝕀 ⊗ X ≃ X
  ρ : ∀ X : C, X ⊗ 𝕀 ≃ X
  triangle : ∀ (X Y : C), (α X 𝕀 Y).toMorphism ≫ (𝟙 X ⨂ «λ» Y) = ρ X ⨂ 𝟙 Y
  pentagon : ∀ (W X Y Z),
    (α W X Y ⨂ 𝟙 Z) ≫ (α W (X ⊗ Y) Z).toMorphism ≫ (𝟙 W ⨂ α X Y Z) =
    (α (W ⊗ X) Y Z).toMorphism ≫ (α W X (Y ⊗ Z)).toMorphism

instance : Category (Type u) where
  arrow X Y := X → Y
  id X := fun (x : X) => x
  comp := fun f g => g ∘ f
  id_comp {x y} f := by simp; ext t; simp
  comp_id {x y} f := by simp; ext t; simp
  assoc {w x y z h g f} := by simp; ext t; simp
@[simp]
def functor_tensor [Category C] :
    (C ⥤ C × C ⥤ C) ⥤ (C ⥤ C) where
  omap x := Functor.comp x.1 x.2
  fmap {F G} η := ⟨fun X => F.2.fmap (η.1.component X) ≫ (η.2.component (G.1 X)),
      fun {X Y} f => by
        simp [Functor.comp]
        rw [← Category.assoc]
        rw [← Functor.map_comp]
        rw [η.1.naturality]
        rw [Functor.map_comp]
        rw [Category.assoc]
        rw [η.2.naturality]
        rw [← Category.assoc]
    ⟩
  map_id F := by
    simp
    congr
    ext t
    simp [CatIdMorphism.id, NatTrans.id, Functor.comp]
    apply F.2.map_id
  map_comp {F G H} η μ := by
    simp
    congr
    ext X
    simp [CatIdMorphism.id, NatTrans.id, CatComp.comp, NatTrans.comp, Functor.comp]
    rw [Functor.map_comp]
    rw [Category.assoc]
    rw [Category.assoc]
    congr 1
    rw [← Category.assoc]
    rw [← Category.assoc]
    congr 1
    rw [η.2.naturality]

instance : MonoidalCategory (Type u ⥤ Type u) where
  tensor := functor_tensor
  tensor_id := Functor.id (Type u)
  α X Y Z := by
    refine Isomorphism.of_eq ?_
    simp [functor_tensor, Functor.comp]
    apply And.intro
    . ext; simp
    . ext; simp
  «λ» X := Isomorphism.of_eq (by congr)
  ρ X := Isomorphism.of_eq (by congr)
  triangle X Y := by
    simp [Isomorphism.of_eq]
    congr
  pentagon W X Y Z := by
    simp [Isomorphism.of_eq]
    simp [CatIdMorphism.id, NatTrans.id]
    simp [functor_tensor, Functor.comp]
    simp [CatComp.comp, NatTrans.comp]
    congr
    ext T x
    simp
    have := X.map_id (W T)
    simp only [CatIdMorphism.id, NatTrans.id] at this
    rw [this]
    have := Y.map_id (X.omap (W.omap T))
    simp only [CatIdMorphism.id, NatTrans.id] at this
    rw [this]
    have := Z.map_id (Y.omap (X.omap (W.omap T)))
    simp only [CatIdMorphism.id, NatTrans.id] at this
    rw [this]

class Monad [MonoidalCategory C] (M : C) where
  η : 𝕀 ⟶ M
  μ : M ⊗ M ⟶ M
  commute : (MonoidalCategory.α M M M).toMorphism ≫ 𝟙 M ⨂ μ ≫ μ = μ ⨂ 𝟙 M ≫ μ
  id_left : η ⨂ 𝟙 M ≫ μ = (MonoidalCategory.«λ» M).toMorphism
  id_right : 𝟙 M ⨂ η ≫ μ = (MonoidalCategory.ρ M).toMorphism

@[simp]
instance functor_option : Functor Type Type where
  omap := Option
  fmap := Option.map
  map_id X := by
    simp [CatIdMorphism.id]
    unfold Option.map
    funext x
    cases x <;> simp
  map_comp {X Y Z} f g := by simp [CatComp.comp]

instance : Monad (C := Type ⥤ Type) functor_option where
  η := by
    simp [functor_option]
    refine ⟨?_, ?_⟩
    . intro X
      simp [Quiver.arrow]
      exact Option.some
    . intro X Y f
      simp [CatComp.comp, MonoidalCategoryStruct.tensor_id, Functor.id]
      unfold Option.map
      funext x
      simp
  μ := by
    refine ⟨?_, ?_⟩
    . intro X
      exact Option.join
    . intro X Y f
      simp [MonoidalCategoryStruct.tensor]
      simp [Functor.comp]
      simp [CatComp.comp]
      funext x
      simp only [Function.comp_def]
      rw [Option.join_map_eq_map_join]
  commute := by
    simp [MonoidalCategory.α]
    simp [Isomorphism.of_eq]
    simp [CatIdMorphism.id]
    simp [CatComp.comp, NatTrans.comp]
    congr
    funext X
    simp [MonoidalCategoryStruct.tensor]
    simp [Functor.comp, CatComp.comp]
    funext x
    simp only [Function.comp_def]
    simp only [Option.join_map_eq_map_join]
    simp [Option.map]
    cases x with
    | none =>
      simp
    | some x =>
      simp
      cases x with
      | none =>
        simp
      | some x =>
        simp
  id_left := by
    simp [CatComp.comp, NatTrans.comp]
    congr
    funext X x
    simp [MonoidalCategoryStruct.tensor] at x
    simp [MonoidalCategoryStruct.tensor]
    simp [Functor.comp]
    simp [CatIdMorphism.id]
    simp [CatComp.comp, NatTrans.comp]
    simp [Option.map]
    cases x <;> simp
  id_right := by
    simp [CatComp.comp, NatTrans.comp]
    congr

end CT
