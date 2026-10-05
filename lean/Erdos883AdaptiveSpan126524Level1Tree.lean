import Erdos883AdaptiveSpan126524Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_1 : adaptiveNumericSpans126524_1.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_1 : adaptiveSpanEven126524_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_1 : adaptiveSpanEven126524_1.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_1 : adaptiveSpanEven126524_1.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_1 : adaptiveSpanWhole126524_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_1 : adaptiveSpanWhole126524_1.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_1 : adaptiveSpanWhole126524_1.spans = coreWholeSpans 0 adaptiveNumericSpans126524_1 := by
  decide +kernel
end Erdos883Verified
