import Erdos883AdaptiveCertificate2478Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2478_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 24034399157747630412286039002121668355474589161501638566754432579468978124759529434860395869885015713148990401861771355452387863817426331359533571852640464101438080094669922268754522566791154106191341666530856964497574196472660579849144434939955973826252406766549242973027351198070904462116284006528
def adaptiveNumericSpans2478_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2478_2Chunk0].flatten
def adaptiveSpanEven2478_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1239 0 adaptiveNumericSpans2478_2)
def adaptiveSpanWhole2478_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2478_2)
theorem adaptiveSpanNumericCheck2478_2 : coreNumericSpansCheck 2418 7 720 1001 adaptiveNumericSpans2478_2 adaptiveRows2478 = true := by decide +kernel
theorem adaptiveSpanEvenCache2478_2 : adaptiveSpanEven2478_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2478_2 : adaptiveSpanEven2478_2.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2478_2 : adaptiveSpanEven2478_2.spans = coreEvenSpans 1239 0 adaptiveNumericSpans2478_2 := by decide +kernel
theorem adaptiveSpanWholeCache2478_2 : adaptiveSpanWhole2478_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2478_2 : adaptiveSpanWhole2478_2.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2478_2 : adaptiveSpanWhole2478_2.spans = coreWholeSpans 0 adaptiveNumericSpans2478_2 := by decide +kernel
def adaptiveNumericSpans2478_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 24034399157747630412286039002121668355474589161501638566754432579468978124759529434860395869885015713148990401861771355452387863817426331359533571852640464101438080094669922268754522847530582122429224162513007378632418569555356908399030551388163664625330804439685629775741590277621377347008375816320
def adaptiveNumericSpans2478_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2478_3Chunk0].flatten
def adaptiveSpanEven2478_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1239 0 adaptiveNumericSpans2478_3)
def adaptiveSpanWhole2478_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2478_3)
theorem adaptiveSpanNumericCheck2478_3 : coreNumericSpansCheck 2418 7 1920 2431 adaptiveNumericSpans2478_3 adaptiveRows2478 = true := by decide +kernel
theorem adaptiveSpanEvenCache2478_3 : adaptiveSpanEven2478_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2478_3 : adaptiveSpanEven2478_3.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2478_3 : adaptiveSpanEven2478_3.spans = coreEvenSpans 1239 0 adaptiveNumericSpans2478_3 := by decide +kernel
theorem adaptiveSpanWholeCache2478_3 : adaptiveSpanWhole2478_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2478_3 : adaptiveSpanWhole2478_3.domainCheck 1239 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2478_3 : adaptiveSpanWhole2478_3.spans = coreWholeSpans 0 adaptiveNumericSpans2478_3 := by decide +kernel
end Erdos883Verified
