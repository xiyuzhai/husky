use crate::path::major_item::{
    connection::MajorItemConnection, form::MajorFormPath, trai::TraitPath, ty::TypePath,
};
#[cfg(test)]
use crate::*;
use husky_coword::{coword_menu, Ident};
use husky_entity_kind::{MajorFormKind, TypeKind};
use husky_vfs::jar::VfsDb;
use husky_vfs::toolchain::Toolchain;

#[salsa::tracked(return_ref)]
pub fn item_path_menu(db: &::salsa::Db, toolchain: Toolchain) -> ItemPathMenu {
    ItemPathMenu::new(db, toolchain)
}

#[derive(Debug, PartialEq, Eq)]
pub struct ItemPathMenu {
    task_ty_var_path: MajorFormPath,
    task_static_var_path: MajorFormPath,
    // core::ops::Add	The addition operator +.
    add_trai_path: TraitPath,
    // core::ops::AddAssign	The addition assignment operator +=.
    add_assign_trai_path: TraitPath,
    // core::ops::BitAnd	The bitwise AND operator &.
    bit_and_trai_path: TraitPath,
    // core::ops::BitAndAssign	The bitwise AND assignment operator &=.
    bit_and_assign_trai_path: TraitPath,
    // core::ops::BitOr	The bitwise OR operator |.
    bit_or_trai_path: TraitPath,
    // core::ops::BitOrAssign	The bitwise OR assignment operator |=.
    bit_or_assign_trai_path: TraitPath,
    // core::ops::BitXor	The bitwise XOR operator ^.
    bit_xor_trai_path: TraitPath,
    // core::ops::BitXorAssign	The bitwise XOR assignment operator ^=.
    bit_xor_assign_trai_path: TraitPath,
    // core::ops::Div	The division operator /.
    div_trai_path: TraitPath,
    // core::ops::DivAssign	The division assignment operator /=.
    div_assign_trai_path: TraitPath,
    // core::ops::IntIndex
    int_index_trai_path: TraitPath,
    // core::ops::Mul	The multiplication operator *.
    mul_trai_path: TraitPath,
    // core::ops::MulAssign	The multiplication assignment operator *=.
    mul_assign_trai_path: TraitPath,
    // core::ops::Neg	The unary negation operator -.
    neg_trai_path: TraitPath,
    // Not	The unary logical negation operator !.
    not_trai_path: TraitPath,
    unveil_trai_path: TraitPath,
    debug_trai_path: TraitPath,
    clone_trai_path: TraitPath,
    copy_trai_path: TraitPath,
    pub partial_eq_trai_path: TraitPath,
    pub eq_trai_path: TraitPath,
    pub partial_ord_trai_path: TraitPath,
    pub ord_trai_path: TraitPath,
    // hash_trai_path: TraitPath,
    default_trai_path: TraitPath,
    visualize_trai_path: TraitPath,
    option_ty_path: TypePath,
    result_ty_path: TypePath,
    slice_ty_path: TypePath,
    cyclic_slice_ty_path: TypePath,
    string_literal_ty_path: TypePath,
    str_ty_path: TypePath,
    ref_ty_path: TypePath,
    ref_mut_ty_path: TypePath,
    at_ty_path: TypePath,
    universe_ty_path: TypePath,
    vec_ty_path: TypePath,
    array_ty_path: TypePath,
    leash_ty_path: TypePath,
    // prelude
    unit_ty_path: TypePath,
    never_ty_path: TypePath,
    bool_ty_path: TypePath,
    i8_ty_path: TypePath,
    i16_ty_path: TypePath,
    i32_ty_path: TypePath,
    i64_ty_path: TypePath,
    i128_ty_path: TypePath,
    isize_ty_path: TypePath,
    f32_ty_path: TypePath,
    f64_ty_path: TypePath,
    r8_ty_path: TypePath,
    r16_ty_path: TypePath,
    r32_ty_path: TypePath,
    r64_ty_path: TypePath,
    r128_ty_path: TypePath,
    rsize_ty_path: TypePath,
    u8_ty_path: TypePath,
    u16_ty_path: TypePath,
    u32_ty_path: TypePath,
    u64_ty_path: TypePath,
    u128_ty_path: TypePath,
    usize_ty_path: TypePath,
    visual_ty_path: TypePath,
    trai_ty_path: TypePath,
    lifetime_ty_path: TypePath,
    place_ty_path: TypePath,
    module_ty_path: TypePath,
    ml_backend_ty_path: TypePath,
    cv2d_frontend_ty_path: TypePath,
    cv3d_frontend_ty_path: TypePath,
    nlp_frontend_ty_path: TypePath,
    rl2d_frontend_ty_path: TypePath,
}

impl ItemPathMenu {
    pub(crate) fn new(db: &::salsa::Db, toolchain: Toolchain) -> Self {
        let coword_menu = coword_menu(db);
        let path_menu = db.vfs_path_menu(toolchain);
        let core_ops = path_menu.core_ops().inner();
        let core_option = path_menu.core_option().inner();
        let core_slice = path_menu.core_slice().inner();
        let core_str = path_menu.core_str().inner();
        let core_basic = path_menu.core_basic().inner();
        let core_clone = path_menu.core_clone().inner();
        let core_cmp = path_menu.core_cmp().inner();
        let core_fmt = path_menu.core_fmt().inner();
        let core_result = path_menu.core_result().inner();
        let core_default = path_menu.core_default().inner();
        let core_marker = path_menu.core_marker().inner();
        let core_num = path_menu.core_num().inner();
        let core_raw_bits = path_menu.core_raw_bits().inner();
        let core_mem = path_menu.core_mem().inner();
        let core_task = path_menu.core_task().inner();
        let core_vec = path_menu.core_vec().inner();
        let core_array = path_menu.core_array().inner();
        let core_visual = path_menu.core_visual().inner();
        let core_backend = path_menu.core_backend().inner();
        let core_frontend = path_menu.core_frontend().inner();
        macro_rules! mk {
            ($m: ident, enum $ident: ident) => {{
                TypePath::new(
                    $m,
                    Ident::from_ref(db, stringify!($ident)).unwrap(),
                    MajorItemConnection::Connected,
                    TypeKind::Enum,
                    db,
                )
            }};
            ($m: ident, struct $ident: ident) => {{
                TypePath::new(
                    $m,
                    Ident::from_ref(db, stringify!($ident)).unwrap(),
                    MajorItemConnection::Connected,
                    TypeKind::Struct,
                    db,
                )
            }};
            ($m: ident, extern $ident: ident) => {{
                TypePath::new(
                    $m,
                    Ident::from_ref(db, stringify!($ident)).unwrap(),
                    MajorItemConnection::Connected,
                    TypeKind::Extern,
                    db,
                )
            }};
            ($m: ident, trait $ident: ident) => {{
                TraitPath::new(
                    $m,
                    Ident::from_ref(db, stringify!($ident)).unwrap(),
                    MajorItemConnection::Connected,
                    db,
                )
            }};
            ($m: ident, type $ident: ident) => {{
                MajorFormPath::new(
                    $m,
                    Ident::from_ref(db, stringify!($ident)).unwrap(),
                    MajorItemConnection::Connected,
                    MajorFormKind::TypeAlias,
                    db,
                )
            }};
            ($m: ident, type var $ident: ident) => {{
                MajorFormPath::new(
                    $m,
                    Ident::from_ref(db, stringify!($ident)).unwrap(),
                    MajorItemConnection::Connected,
                    MajorFormKind::TypeVar,
                    db,
                )
            }};
            ($m: ident, static var $ident: ident) => {{
                MajorFormPath::new(
                    $m,
                    Ident::from_ref(db, stringify!($ident)).unwrap(),
                    MajorItemConnection::Connected,
                    MajorFormKind::StaticVar,
                    db,
                )
            }};
        }
        Self {
            task_ty_var_path: mk!(core_task, type var Task),
            task_static_var_path: mk!(core_task, static var Task),
            unit_ty_path: mk!(core_basic, extern unit),
            never_ty_path: mk!(core_basic, extern never),
            bool_ty_path: mk!(core_basic, extern bool),
            i8_ty_path: mk!(core_num, extern i8),
            i16_ty_path: mk!(core_num, extern i16),
            i32_ty_path: mk!(core_num, extern i32),
            i64_ty_path: mk!(core_num, extern i64),
            i128_ty_path: mk!(core_num, extern i128),
            isize_ty_path: mk!(core_num, extern isize),
            u8_ty_path: mk!(core_num, extern u8),
            u16_ty_path: mk!(core_num, extern u16),
            u32_ty_path: mk!(core_num, extern u32),
            u64_ty_path: mk!(core_num, extern u64),
            u128_ty_path: mk!(core_num, extern u128),
            usize_ty_path: mk!(core_num, extern usize),
            r8_ty_path: mk!(core_raw_bits, extern r8),
            r16_ty_path: mk!(core_raw_bits, extern r16),
            r32_ty_path: mk!(core_raw_bits, extern r32),
            r64_ty_path: mk!(core_raw_bits, extern r64),
            r128_ty_path: mk!(core_raw_bits, extern r128),
            rsize_ty_path: mk!(core_raw_bits, extern rsize),
            f32_ty_path: mk!(core_num, extern f32),
            f64_ty_path: mk!(core_num, extern f64),
            trai_ty_path: mk!(core_basic, extern Trait),
            module_ty_path: mk!(core_basic, extern Module),
            lifetime_ty_path: mk!(core_basic, extern Lifetime),
            place_ty_path: mk!(core_basic, extern Place),
            option_ty_path: mk!(core_option, enum Option),
            slice_ty_path: mk!(core_slice, extern Slice),
            cyclic_slice_ty_path: mk!(core_slice, extern CyclicSlice),
            string_literal_ty_path: mk!(core_str, extern StringLiteral),
            str_ty_path: mk!(core_str, extern str),
            ref_ty_path: mk!(core_mem, extern Ref),
            ref_mut_ty_path: mk!(core_mem, extern RefMut),
            leash_ty_path: mk!(core_mem, extern Leash),
            at_ty_path: mk!(core_mem, extern At),
            universe_ty_path: mk!(core_basic, extern Universe),
            visual_ty_path: mk!(core_visual, extern Visual),
            vec_ty_path: mk!(core_vec, extern Vec),
            array_ty_path: mk!(core_array, extern Array),
            add_trai_path: mk!(core_ops, trait Add),
            add_assign_trai_path: mk!(core_ops, trait AddAssign),
            bit_and_trai_path: mk!(core_ops, trait BitAnd),
            bit_and_assign_trai_path: mk!(core_ops, trait BitAndAssign),
            bit_or_trai_path: mk!(core_ops, trait BitOr),
            bit_or_assign_trai_path: mk!(core_ops, trait BitOrAssign),
            bit_xor_trai_path: mk!(core_ops, trait BitXor),
            bit_xor_assign_trai_path: mk!(core_ops, trait BitXorAssign),
            div_trai_path: mk!(core_ops, trait Div),
            div_assign_trai_path: mk!(core_ops, trait DivAssign),
            int_index_trai_path: mk!(core_ops, trait IntIndex),
            mul_trai_path: mk!(core_ops, trait Mul),
            mul_assign_trai_path: mk!(core_ops, trait MulAssign),
            neg_trai_path: mk!(core_ops, trait Neg),
            not_trai_path: mk!(core_ops, trait Not),
            unveil_trai_path: mk!(core_ops, trait Unveil),
            debug_trai_path: mk!(core_fmt, trait Debug),
            clone_trai_path: mk!(core_clone, trait Clone),
            copy_trai_path: mk!(core_marker, trait Copy),
            partial_eq_trai_path: mk!(core_cmp, trait PartialEq),
            eq_trai_path: mk!(core_cmp, trait Eq),
            partial_ord_trai_path: mk!(core_cmp, trait PartialOrd),
            ord_trai_path: mk!(core_cmp, trait Ord),
            default_trai_path: mk!(core_default, trait Default),
            visualize_trai_path: mk!(core_visual, trait Visualize),
            result_ty_path: mk!(core_result, enum Result),
            ml_backend_ty_path: mk!(core_backend, extern MlBackend),
            cv2d_frontend_ty_path: mk!(core_frontend, extern Cv2dFrontend),
            cv3d_frontend_ty_path: mk!(core_frontend, extern Cv3dFrontend),
            nlp_frontend_ty_path: mk!(core_frontend, extern NlpFrontend),
            rl2d_frontend_ty_path: mk!(core_frontend, extern Rl2dFrontend),
        }
    }

    pub fn unit_ty_path(&self) -> TypePath {
        self.unit_ty_path
    }

    pub fn never_ty_path(&self) -> TypePath {
        self.never_ty_path
    }

    pub fn bool_ty_path(&self) -> TypePath {
        self.bool_ty_path
    }

    pub fn i8_ty_path(&self) -> TypePath {
        self.i8_ty_path
    }

    pub fn i16_ty_path(&self) -> TypePath {
        self.i16_ty_path
    }

    pub fn i32_ty_path(&self) -> TypePath {
        self.i32_ty_path
    }

    pub fn i64_ty_path(&self) -> TypePath {
        self.i64_ty_path
    }

    pub fn i128_ty_path(&self) -> TypePath {
        self.i128_ty_path
    }

    pub fn isize_ty_path(&self) -> TypePath {
        self.isize_ty_path
    }

    pub fn u8_ty_path(&self) -> TypePath {
        self.u8_ty_path
    }

    pub fn u16_ty_path(&self) -> TypePath {
        self.u16_ty_path
    }

    pub fn u32_ty_path(&self) -> TypePath {
        self.u32_ty_path
    }

    pub fn u64_ty_path(&self) -> TypePath {
        self.u64_ty_path
    }

    pub fn u128_ty_path(&self) -> TypePath {
        self.u128_ty_path
    }

    pub fn usize_ty_path(&self) -> TypePath {
        self.usize_ty_path
    }

    pub fn r8_ty_path(&self) -> TypePath {
        self.r8_ty_path
    }

    pub fn r16_ty_path(&self) -> TypePath {
        self.r16_ty_path
    }

    pub fn r32_ty_path(&self) -> TypePath {
        self.r32_ty_path
    }

    pub fn r64_ty_path(&self) -> TypePath {
        self.r64_ty_path
    }

    pub fn r128_ty_path(&self) -> TypePath {
        self.r128_ty_path
    }

    pub fn rsize_ty_path(&self) -> TypePath {
        self.rsize_ty_path
    }

    pub fn f32_ty_path(&self) -> TypePath {
        self.f32_ty_path
    }

    pub fn f64_ty_path(&self) -> TypePath {
        self.f64_ty_path
    }

    pub fn trai_ty_path(&self) -> TypePath {
        self.trai_ty_path
    }

    pub fn module_ty_path(&self) -> TypePath {
        self.module_ty_path
    }

    pub fn lifetime_ty_path(&self) -> TypePath {
        self.lifetime_ty_path
    }

    pub fn place_ty_path(&self) -> TypePath {
        self.place_ty_path
    }

    pub fn option_ty_path(&self) -> TypePath {
        self.option_ty_path
    }

    pub fn slice_ty_path(&self) -> TypePath {
        self.slice_ty_path
    }

    pub fn cyclic_slice_ty_path(&self) -> TypePath {
        self.cyclic_slice_ty_path
    }

    pub fn string_literal_ty_path(&self) -> TypePath {
        self.string_literal_ty_path
    }

    pub fn str_ty_path(&self) -> TypePath {
        self.str_ty_path
    }

    pub fn ref_ty_path(&self) -> TypePath {
        self.ref_ty_path
    }

    pub fn ref_mut_ty_path(&self) -> TypePath {
        self.ref_mut_ty_path
    }

    pub fn at_ty_path(&self) -> TypePath {
        self.at_ty_path
    }

    pub fn result_ty_path(&self) -> TypePath {
        self.result_ty_path
    }

    pub fn universe_ty_path(&self) -> TypePath {
        self.universe_ty_path
    }

    pub fn vec_ty_path(&self) -> TypePath {
        self.vec_ty_path
    }

    pub fn array_ty_path(&self) -> TypePath {
        self.array_ty_path
    }

    pub fn leash_ty_path(&self) -> TypePath {
        self.leash_ty_path
    }

    pub fn add_trai_path(&self) -> TraitPath {
        self.add_trai_path
    }

    pub fn add_assign_trai_path(&self) -> TraitPath {
        self.add_assign_trai_path
    }

    pub fn bit_and_trai_path(&self) -> TraitPath {
        self.bit_and_trai_path
    }

    pub fn bit_and_assign_trai_path(&self) -> TraitPath {
        self.bit_and_assign_trai_path
    }

    pub fn bit_or_trai_path(&self) -> TraitPath {
        self.bit_or_trai_path
    }

    pub fn bit_or_assign_trai_path(&self) -> TraitPath {
        self.bit_or_assign_trai_path
    }

    pub fn bit_xor_trai_path(&self) -> TraitPath {
        self.bit_xor_trai_path
    }

    pub fn bit_xor_assign_trai_path(&self) -> TraitPath {
        self.bit_xor_assign_trai_path
    }

    pub fn div_trai_path(&self) -> TraitPath {
        self.div_trai_path
    }

    pub fn div_assign_trai_path(&self) -> TraitPath {
        self.div_assign_trai_path
    }

    pub fn int_index_trai_path(&self) -> TraitPath {
        self.int_index_trai_path
    }

    pub fn mul_trai_path(&self) -> TraitPath {
        self.mul_trai_path
    }

    pub fn mul_assign_trai_path(&self) -> TraitPath {
        self.mul_assign_trai_path
    }

    pub fn neg_trai_path(&self) -> TraitPath {
        self.neg_trai_path
    }

    pub fn not_trai_path(&self) -> TraitPath {
        self.not_trai_path
    }

    pub fn unveil_trai_path(&self) -> TraitPath {
        self.unveil_trai_path
    }

    pub fn debug_trai_path(&self) -> TraitPath {
        self.debug_trai_path
    }

    pub fn clone_trai_path(&self) -> TraitPath {
        self.clone_trai_path
    }

    pub fn copy_trai_path(&self) -> TraitPath {
        self.copy_trai_path
    }

    pub fn default_trai_path(&self) -> TraitPath {
        self.default_trai_path
    }

    pub fn visualize_trai_path(&self) -> TraitPath {
        self.visualize_trai_path
    }

    pub fn visual_ty_path(&self) -> TypePath {
        self.visual_ty_path
    }

    pub fn task_ty_var_path(&self) -> MajorFormPath {
        self.task_ty_var_path
    }

    pub fn task_static_var_path(&self) -> MajorFormPath {
        self.task_static_var_path
    }
}

#[test]
fn menu_works() {
    use husky_vfs::test_helpers::jar::VfsTestUtilsDb;

    let db = DB::default();
    let db = &*db;
    let toolchain = db.dev_toolchain().unwrap();
    let item_path_menu = item_path_menu(db, toolchain);
    assert_eq!(item_path_menu.add_trai_path().show(db), "core::ops::Add");
    assert_eq!(
        item_path_menu.add_assign_trai_path().show(db),
        "core::ops::AddAssign"
    );
    assert_eq!(
        item_path_menu.bit_and_trai_path().show(db),
        "core::ops::BitAnd"
    );
    assert_eq!(
        item_path_menu.bit_and_assign_trai_path().show(db),
        "core::ops::BitAndAssign"
    );
    assert_eq!(
        item_path_menu.bit_or_trai_path().show(db),
        "core::ops::BitOr"
    );
    assert_eq!(
        item_path_menu.bit_or_assign_trai_path().show(db),
        "core::ops::BitOrAssign"
    );
    assert_eq!(
        item_path_menu.bit_xor_trai_path().show(db),
        "core::ops::BitXor"
    );
    assert_eq!(
        item_path_menu.bit_xor_assign_trai_path().show(db),
        "core::ops::BitXorAssign"
    );
    assert_eq!(item_path_menu.div_trai_path().show(db), "core::ops::Div");
    assert_eq!(
        item_path_menu.div_assign_trai_path().show(db),
        "core::ops::DivAssign"
    );
    assert_eq!(item_path_menu.mul_trai_path().show(db), "core::ops::Mul");
    assert_eq!(
        item_path_menu.mul_assign_trai_path().show(db),
        "core::ops::MulAssign"
    );
    assert_eq!(item_path_menu.neg_trai_path().show(db), "core::ops::Neg");
    assert_eq!(item_path_menu.not_trai_path().show(db), "core::ops::Not");
}
