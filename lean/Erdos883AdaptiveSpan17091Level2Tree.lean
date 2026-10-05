import Erdos883AdaptiveSpan17091Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_2 : adaptiveNumericSpans17091_2.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_2 : adaptiveSpanEven17091_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_2 : adaptiveSpanEven17091_2.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_2 : adaptiveSpanEven17091_2.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_2 : adaptiveSpanWhole17091_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_2 : adaptiveSpanWhole17091_2.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_2 : adaptiveSpanWhole17091_2.spans = coreWholeSpans 0 adaptiveNumericSpans17091_2 := by
  decide +kernel
end Erdos883Verified
