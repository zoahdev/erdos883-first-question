import Erdos883AdaptiveSpan17091Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_8 : adaptiveNumericSpans17091_8.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_8 : adaptiveSpanEven17091_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_8 : adaptiveSpanEven17091_8.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_8 : adaptiveSpanEven17091_8.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_8 : adaptiveSpanWhole17091_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_8 : adaptiveSpanWhole17091_8.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_8 : adaptiveSpanWhole17091_8.spans = coreWholeSpans 0 adaptiveNumericSpans17091_8 := by
  decide +kernel
end Erdos883Verified
