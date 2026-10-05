import Erdos883AdaptiveSpan78559Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_8 : adaptiveNumericSpans78559_8.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_8 : adaptiveSpanEven78559_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_8 : adaptiveSpanEven78559_8.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_8 : adaptiveSpanEven78559_8.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_8 : adaptiveSpanWhole78559_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_8 : adaptiveSpanWhole78559_8.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_8 : adaptiveSpanWhole78559_8.spans = coreWholeSpans 0 adaptiveNumericSpans78559_8 := by
  decide +kernel
end Erdos883Verified
