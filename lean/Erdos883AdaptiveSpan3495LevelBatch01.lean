import Erdos883AdaptiveCertificate3495Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3495_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 86101614106532590883186547962610017769704109267957953917562782689721062870049566313551785120504103981512164571249015315614898595695894109518029604496553951465744812095288854289971500224904224022050454692038970520825996642649459056667536663713499147499424429279509992850025355259625555008576346112797850360761396418261515459605601119443627286454397106295179878411774574425353275478709712227789348171179428159318562701440
def adaptiveNumericSpans3495_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans3495_2Chunk0].flatten
def adaptiveSpanEven3495_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1748 0 adaptiveNumericSpans3495_2)
def adaptiveSpanWhole3495_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3495_2)
theorem adaptiveSpanNumericCheck3495_2 : coreNumericSpansCheck 3329 7 720 1001 adaptiveNumericSpans3495_2 adaptiveRows3495 = true := by decide +kernel
theorem adaptiveSpanEvenCache3495_2 : adaptiveSpanEven3495_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3495_2 : adaptiveSpanEven3495_2.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3495_2 : adaptiveSpanEven3495_2.spans = coreEvenSpans 1748 0 adaptiveNumericSpans3495_2 := by decide +kernel
theorem adaptiveSpanWholeCache3495_2 : adaptiveSpanWhole3495_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3495_2 : adaptiveSpanWhole3495_2.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3495_2 : adaptiveSpanWhole3495_2.spans = coreWholeSpans 0 adaptiveNumericSpans3495_2 := by decide +kernel
def adaptiveNumericSpans3495_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 86101614106532590883186547962610017769704109267957953917562782689721062870049566313551785120504103981512164571249015315614898595695894109518029604496553951465744812095288854289971500224904224022050454692038970520825996642649459056667536663714140228201959710217518123563833137370012742599928466600183236348264956620592599527076112624656313029750512064227046473488761231617170386891118065746179350766494232590424026906752
def adaptiveNumericSpans3495_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans3495_3Chunk0].flatten
def adaptiveSpanEven3495_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1748 0 adaptiveNumericSpans3495_3)
def adaptiveSpanWhole3495_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3495_3)
theorem adaptiveSpanNumericCheck3495_3 : coreNumericSpansCheck 3329 7 1920 2431 adaptiveNumericSpans3495_3 adaptiveRows3495 = true := by decide +kernel
theorem adaptiveSpanEvenCache3495_3 : adaptiveSpanEven3495_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3495_3 : adaptiveSpanEven3495_3.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3495_3 : adaptiveSpanEven3495_3.spans = coreEvenSpans 1748 0 adaptiveNumericSpans3495_3 := by decide +kernel
theorem adaptiveSpanWholeCache3495_3 : adaptiveSpanWhole3495_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3495_3 : adaptiveSpanWhole3495_3.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3495_3 : adaptiveSpanWhole3495_3.spans = coreWholeSpans 0 adaptiveNumericSpans3495_3 := by decide +kernel
end Erdos883Verified
