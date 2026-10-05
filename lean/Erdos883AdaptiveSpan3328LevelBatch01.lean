import Erdos883AdaptiveCertificate3328Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3328_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 64612473238884043844036274094572330931779685473098262151363847361524306853792612836712371793548759446107220039712269185682705360769706781772925338349071600930076784275757106200330770663432915626768998365973807841679352453903678566611128919125665141078600321032984915537010361051379700921529347937078025239024600330780191110817897675213823256634189968467262584231624711794232852656362094720
def adaptiveNumericSpans3328_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans3328_2Chunk0].flatten
def adaptiveSpanEven3328_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1664 0 adaptiveNumericSpans3328_2)
def adaptiveSpanWhole3328_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3328_2)
theorem adaptiveSpanNumericCheck3328_2 : coreNumericSpansCheck 3170 7 720 1001 adaptiveNumericSpans3328_2 adaptiveRows3328 = true := by decide +kernel
theorem adaptiveSpanEvenCache3328_2 : adaptiveSpanEven3328_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3328_2 : adaptiveSpanEven3328_2.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3328_2 : adaptiveSpanEven3328_2.spans = coreEvenSpans 1664 0 adaptiveNumericSpans3328_2 := by decide +kernel
theorem adaptiveSpanWholeCache3328_2 : adaptiveSpanWhole3328_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3328_2 : adaptiveSpanWhole3328_2.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3328_2 : adaptiveSpanWhole3328_2.spans = coreWholeSpans 0 adaptiveNumericSpans3328_2 := by decide +kernel
def adaptiveNumericSpans3328_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 64612473238884043844036274094572330931779685473098262151363847361524306853792612836712371793548759446107220039712269185682705360769706781772925338349071600930076784275757106200330770663432915626768998365973807841984063651929115495792239410201406575761854489507824385478944321001736119292393283152644967355498160640248416148455048828605891182160398331096628289486909418357301180985960824960
def adaptiveNumericSpans3328_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans3328_3Chunk0].flatten
def adaptiveSpanEven3328_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1664 0 adaptiveNumericSpans3328_3)
def adaptiveSpanWhole3328_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3328_3)
theorem adaptiveSpanNumericCheck3328_3 : coreNumericSpansCheck 3170 7 1920 2431 adaptiveNumericSpans3328_3 adaptiveRows3328 = true := by decide +kernel
theorem adaptiveSpanEvenCache3328_3 : adaptiveSpanEven3328_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3328_3 : adaptiveSpanEven3328_3.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3328_3 : adaptiveSpanEven3328_3.spans = coreEvenSpans 1664 0 adaptiveNumericSpans3328_3 := by decide +kernel
theorem adaptiveSpanWholeCache3328_3 : adaptiveSpanWhole3328_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3328_3 : adaptiveSpanWhole3328_3.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3328_3 : adaptiveSpanWhole3328_3.spans = coreWholeSpans 0 adaptiveNumericSpans3328_3 := by decide +kernel
end Erdos883Verified
