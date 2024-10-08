use crate::*;

impl AarchRegister {
    pub fn class(self) -> AarchRegisterClass {
        match self {
            r if AarchRegister::X0 <= r && r <= AarchRegister::XZR
                || AarchRegister::W0 <= r && r <= AarchRegister::WZR =>
            {
                AarchRegisterClass::GeneralPurpose
            }
            AarchRegister::SP | AarchRegister::WSP => AarchRegisterClass::StackPointer,
            r if AarchRegister::Q0 <= r && r <= AarchRegister::Q31
                || AarchRegister::D0 <= r && r <= AarchRegister::D31
                || AarchRegister::S0 <= r && r <= AarchRegister::S31
                || AarchRegister::H0 <= r && r <= AarchRegister::H31
                || AarchRegister::B0 <= r && r <= AarchRegister::B31 =>
            {
                AarchRegisterClass::FloatingPoint
            }
            _ => unreachable!(),
        }
    }
}

#[test]
pub(crate) fn aarch_register_class_works() {
    assert_eq!(
        AarchRegister::X0.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X1.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X2.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X3.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X4.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X5.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X6.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X7.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X8.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X9.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X10.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X11.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X12.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X13.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X14.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X15.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X16.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X17.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X18.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X19.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X20.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X21.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X22.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X23.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X24.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X25.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X26.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X27.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X28.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X29.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::X30.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::XZR.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W0.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W1.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W2.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W3.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W4.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W5.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W6.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W7.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W8.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W9.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W10.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W11.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W12.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W13.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W14.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W15.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W16.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W17.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W18.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W19.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W20.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W21.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W22.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W23.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W24.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W25.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W26.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W27.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W28.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W29.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::W30.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(
        AarchRegister::WZR.class(),
        AarchRegisterClass::GeneralPurpose
    );
    assert_eq!(AarchRegister::SP.class(), AarchRegisterClass::StackPointer);
    assert_eq!(AarchRegister::WSP.class(), AarchRegisterClass::StackPointer);
    assert_eq!(AarchRegister::Q0.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q1.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q2.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q3.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q4.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q5.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q6.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q7.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q8.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::Q9.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(
        AarchRegister::Q10.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q11.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q12.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q13.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q14.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q15.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q16.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q17.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q18.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q19.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q20.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q21.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q22.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q23.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q24.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q25.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q26.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q27.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q28.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q29.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q30.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::Q31.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(AarchRegister::D0.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D1.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D2.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D3.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D4.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D5.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D6.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D7.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D8.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D9.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(
        AarchRegister::D10.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D11.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D12.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D13.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D14.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D15.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D16.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D17.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D18.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D19.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D20.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D21.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D22.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D23.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D24.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D25.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D26.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D27.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D28.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D29.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D30.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D31.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(AarchRegister::S0.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S1.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S2.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S3.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S4.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S5.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S6.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S7.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S8.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::S9.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(
        AarchRegister::S10.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S11.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S12.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S13.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S14.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S15.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S16.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S17.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S18.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S19.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S20.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S21.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S22.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S23.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S24.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S25.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S26.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S27.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S28.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S29.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S30.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::S31.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(AarchRegister::H0.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H1.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H2.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H3.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H4.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H5.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H6.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H7.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H8.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::H9.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(
        AarchRegister::H10.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H11.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H12.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H13.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H14.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H15.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H16.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H17.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H18.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H19.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H20.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H21.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H22.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H23.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H24.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H25.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H26.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H27.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H28.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H29.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H30.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::H31.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(AarchRegister::B0.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B1.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B2.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B3.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B4.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B5.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B6.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B7.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B8.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::B9.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(
        AarchRegister::B10.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B11.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B12.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B13.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B14.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B15.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B16.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B17.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B18.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B19.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B20.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B21.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B22.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B23.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B24.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B25.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B25.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B26.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B27.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B28.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B29.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B30.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::B31.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(AarchRegister::D0.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D1.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D2.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D3.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D4.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D5.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D6.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D7.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D8.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(AarchRegister::D9.class(), AarchRegisterClass::FloatingPoint);
    assert_eq!(
        AarchRegister::D10.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D11.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D12.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D13.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D14.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D15.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D16.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D17.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D18.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D19.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D20.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D21.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D22.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D23.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D24.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D25.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D26.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D27.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D28.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D29.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D30.class(),
        AarchRegisterClass::FloatingPoint
    );
    assert_eq!(
        AarchRegister::D31.class(),
        AarchRegisterClass::FloatingPoint
    );
}
