import Erdos883AdaptiveSpan17091Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_4 : adaptiveNumericSpans17091_4.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_4 : adaptiveSpanEven17091_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_4 : adaptiveSpanEven17091_4.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_4 : adaptiveSpanEven17091_4.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_4 : adaptiveSpanWhole17091_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_4 : adaptiveSpanWhole17091_4.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_4 : adaptiveSpanWhole17091_4.spans = coreWholeSpans 0 adaptiveNumericSpans17091_4 := by
  decide +kernel
end Erdos883Verified
