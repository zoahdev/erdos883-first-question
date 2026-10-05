import Erdos883AdaptiveSpan17091Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_3 : adaptiveNumericSpans17091_3.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_3 : adaptiveSpanEven17091_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_3 : adaptiveSpanEven17091_3.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_3 : adaptiveSpanEven17091_3.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_3 : adaptiveSpanWhole17091_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_3 : adaptiveSpanWhole17091_3.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_3 : adaptiveSpanWhole17091_3.spans = coreWholeSpans 0 adaptiveNumericSpans17091_3 := by
  decide +kernel
end Erdos883Verified
