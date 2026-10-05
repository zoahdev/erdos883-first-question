import Erdos883AdaptiveSpan78559Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_0 : adaptiveNumericSpans78559_0.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_0 : adaptiveSpanEven78559_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_0 : adaptiveSpanEven78559_0.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_0 : adaptiveSpanEven78559_0.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_0 : adaptiveSpanWhole78559_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_0 : adaptiveSpanWhole78559_0.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_0 : adaptiveSpanWhole78559_0.spans = coreWholeSpans 0 adaptiveNumericSpans78559_0 := by
  decide +kernel
end Erdos883Verified
