import Erdos883AdaptiveSpan78559Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_2 : adaptiveNumericSpans78559_2.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_2 : adaptiveSpanEven78559_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_2 : adaptiveSpanEven78559_2.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_2 : adaptiveSpanEven78559_2.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_2 : adaptiveSpanWhole78559_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_2 : adaptiveSpanWhole78559_2.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_2 : adaptiveSpanWhole78559_2.spans = coreWholeSpans 0 adaptiveNumericSpans78559_2 := by
  decide +kernel
end Erdos883Verified
