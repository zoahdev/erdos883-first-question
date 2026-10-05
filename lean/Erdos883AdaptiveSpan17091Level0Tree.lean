import Erdos883AdaptiveSpan17091Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_0 : adaptiveNumericSpans17091_0.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_0 : adaptiveSpanEven17091_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_0 : adaptiveSpanEven17091_0.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_0 : adaptiveSpanEven17091_0.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_0 : adaptiveSpanWhole17091_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_0 : adaptiveSpanWhole17091_0.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_0 : adaptiveSpanWhole17091_0.spans = coreWholeSpans 0 adaptiveNumericSpans17091_0 := by
  decide +kernel
end Erdos883Verified
