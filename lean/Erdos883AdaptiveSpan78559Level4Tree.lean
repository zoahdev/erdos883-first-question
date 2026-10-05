import Erdos883AdaptiveSpan78559Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_4 : adaptiveNumericSpans78559_4.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_4 : adaptiveSpanEven78559_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_4 : adaptiveSpanEven78559_4.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_4 : adaptiveSpanEven78559_4.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_4 : adaptiveSpanWhole78559_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_4 : adaptiveSpanWhole78559_4.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_4 : adaptiveSpanWhole78559_4.spans = coreWholeSpans 0 adaptiveNumericSpans78559_4 := by
  decide +kernel
end Erdos883Verified
