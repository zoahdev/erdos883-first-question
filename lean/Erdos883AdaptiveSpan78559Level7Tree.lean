import Erdos883AdaptiveSpan78559Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_7 : adaptiveNumericSpans78559_7.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_7 : adaptiveSpanEven78559_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_7 : adaptiveSpanEven78559_7.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_7 : adaptiveSpanEven78559_7.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_7 : adaptiveSpanWhole78559_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_7 : adaptiveSpanWhole78559_7.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_7 : adaptiveSpanWhole78559_7.spans = coreWholeSpans 0 adaptiveNumericSpans78559_7 := by
  decide +kernel
end Erdos883Verified
