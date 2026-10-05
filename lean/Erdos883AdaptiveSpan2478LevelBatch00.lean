import Erdos883AdaptiveCertificate2478Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2478_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 30467220518443634875818254011767842576186298317350054722089062776866832476528531330592737695180602667286057071050056612246924191517735535912853639558273689078809669520578529273001125655596727002031683026175020551445996909085757451235014957914806173877190027711901226080471009643120215889316452275726261765973390684353345049591936
def adaptiveNumericSpans2478_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2478_0Chunk0].flatten
def adaptiveSpanEven2478_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1239 0 adaptiveNumericSpans2478_0)
def adaptiveSpanWhole2478_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2478_0)
theorem adaptiveSpanNumericCheck2478_0 : coreNumericSpansCheck 2418 7 480 1155 adaptiveNumericSpans2478_0 adaptiveRows2478 = true := by decide +kernel
theorem adaptiveSpanEvenCache2478_0 : adaptiveSpanEven2478_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2478_0 : adaptiveSpanEven2478_0.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2478_0 : adaptiveSpanEven2478_0.spans = coreEvenSpans 1239 0 adaptiveNumericSpans2478_0 := by decide +kernel
theorem adaptiveSpanWholeCache2478_0 : adaptiveSpanWhole2478_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2478_0 : adaptiveSpanWhole2478_0.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2478_0 : adaptiveSpanWhole2478_0.spans = coreWholeSpans 0 adaptiveNumericSpans2478_0 := by decide +kernel
def adaptiveNumericSpans2478_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 24034399157747630412286039002121668355474589161501638566754432579468978124759529434860395869885015713148990401861771355452387863817426331359533571852640464101438080094669922268754522355005269813239956625702217178371549081202664592609739646698838402369241899888413627275871150258174180232029991338112
def adaptiveNumericSpans2478_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2478_1Chunk0].flatten
def adaptiveSpanEven2478_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1239 0 adaptiveNumericSpans2478_1)
def adaptiveSpanWhole2478_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2478_1)
theorem adaptiveSpanNumericCheck2478_1 : coreNumericSpansCheck 2418 7 240 385 adaptiveNumericSpans2478_1 adaptiveRows2478 = true := by decide +kernel
theorem adaptiveSpanEvenCache2478_1 : adaptiveSpanEven2478_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2478_1 : adaptiveSpanEven2478_1.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2478_1 : adaptiveSpanEven2478_1.spans = coreEvenSpans 1239 0 adaptiveNumericSpans2478_1 := by decide +kernel
theorem adaptiveSpanWholeCache2478_1 : adaptiveSpanWhole2478_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2478_1 : adaptiveSpanWhole2478_1.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2478_1 : adaptiveSpanWhole2478_1.spans = coreWholeSpans 0 adaptiveNumericSpans2478_1 := by decide +kernel
end Erdos883Verified
