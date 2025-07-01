Signatur
 	h,			% 1.HIV-infizierte Menschen (HIV-infected humans)
	v,			% 2.HIV-positiv sein (to be HIV-positive)
	c,			% 3.Einen funktionierenden CCR5-Rezeptor haben (to have functional CCR5-receptor)
	r			% 4.Ein seltenes HIV-Virus, das den CXCR4-Rezeptor nutzt (a rare HIV-virus, using CXCR4-receptor as entry)

Konditionale
HIV5 {
	(c|h),		% 1.Menschen, die sich mit HIV infiziert haben, haben normalerweise einen funktionierenden CCR5-Rezeptor.
	(v|h),		% 2.Menschen, die sich mit HIV infiziert haben, werden normalerweise HIV-positiv.
	(v|c),		% 3.Ein funktionierender CCR5-Rezeptor erlaubt es norma-lerweise, HIV-positiv zu werden.
	(!v|!c),	% 4.Ein nicht funktionierender CCR5-Rezeptor erlaubt es normalerweise nicht, HIV-positiv zu werden.
	(v|h,r,!c)	% 5.HIV-infizierte Menschen, die sich mit einem seltenen HIV-Virus infiziert haben, das den CXCR4-Rezeptor nutzt, werden normalerweise HIV-positiv.
}
