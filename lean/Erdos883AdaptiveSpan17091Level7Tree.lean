import Erdos883AdaptiveSpan17091Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_7 : adaptiveNumericSpans17091_7.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_7 : adaptiveSpanEven17091_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_7 : adaptiveSpanEven17091_7.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_7 : adaptiveSpanEven17091_7.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_7 : adaptiveSpanWhole17091_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_7 : adaptiveSpanWhole17091_7.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_7 : adaptiveSpanWhole17091_7.spans = coreWholeSpans 0 adaptiveNumericSpans17091_7 := by
  decide +kernel
end Erdos883Verified
