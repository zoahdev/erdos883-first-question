import Erdos883AdaptiveSpan78559Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_3 : adaptiveNumericSpans78559_3.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_3 : adaptiveSpanEven78559_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_3 : adaptiveSpanEven78559_3.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_3 : adaptiveSpanEven78559_3.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_3 : adaptiveSpanWhole78559_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_3 : adaptiveSpanWhole78559_3.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_3 : adaptiveSpanWhole78559_3.spans = coreWholeSpans 0 adaptiveNumericSpans78559_3 := by
  decide +kernel
end Erdos883Verified
