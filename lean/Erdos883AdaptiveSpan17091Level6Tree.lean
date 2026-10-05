import Erdos883AdaptiveSpan17091Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_6 : adaptiveNumericSpans17091_6.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_6 : adaptiveSpanEven17091_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_6 : adaptiveSpanEven17091_6.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_6 : adaptiveSpanEven17091_6.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_6 : adaptiveSpanWhole17091_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_6 : adaptiveSpanWhole17091_6.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_6 : adaptiveSpanWhole17091_6.spans = coreWholeSpans 0 adaptiveNumericSpans17091_6 := by
  decide +kernel
end Erdos883Verified
