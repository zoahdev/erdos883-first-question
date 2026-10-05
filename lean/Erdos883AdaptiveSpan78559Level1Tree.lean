import Erdos883AdaptiveSpan78559Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength78559_1 : adaptiveNumericSpans78559_1.length = 593 := by decide +kernel
theorem adaptiveSpanEvenCache78559_1 : adaptiveSpanEven78559_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain78559_1 : adaptiveSpanEven78559_1.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanEvenEntries78559_1 : adaptiveSpanEven78559_1.spans = coreEvenSpans 39280 0 adaptiveNumericSpans78559_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache78559_1 : adaptiveSpanWhole78559_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain78559_1 : adaptiveSpanWhole78559_1.domainCheck 39280 = true := by decide +kernel
theorem adaptiveSpanWholeEntries78559_1 : adaptiveSpanWhole78559_1.spans = coreWholeSpans 0 adaptiveNumericSpans78559_1 := by
  decide +kernel
end Erdos883Verified
