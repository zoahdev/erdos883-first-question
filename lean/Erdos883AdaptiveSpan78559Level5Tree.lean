import Erdos883AdaptiveSpan78559Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_5 : adaptiveNumericSpans78559_5.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_5 : adaptiveSpanEven78559_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_5 : adaptiveSpanEven78559_5.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_5 : adaptiveSpanEven78559_5.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_5 : adaptiveSpanWhole78559_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_5 : adaptiveSpanWhole78559_5.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_5 : adaptiveSpanWhole78559_5.spans = coreWholeSpans 0 adaptiveNumericSpans78559_5 := by
  decide +kernel
end Erdos883Verified
