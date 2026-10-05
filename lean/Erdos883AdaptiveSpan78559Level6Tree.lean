import Erdos883AdaptiveSpan78559Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_6 : adaptiveNumericSpans78559_6.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_6 : adaptiveSpanEven78559_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_6 : adaptiveSpanEven78559_6.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_6 : adaptiveSpanEven78559_6.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_6 : adaptiveSpanWhole78559_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_6 : adaptiveSpanWhole78559_6.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_6 : adaptiveSpanWhole78559_6.spans = coreWholeSpans 0 adaptiveNumericSpans78559_6 := by
  decide +kernel
end Erdos883Verified
