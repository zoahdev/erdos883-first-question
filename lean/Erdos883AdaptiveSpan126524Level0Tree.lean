import Erdos883AdaptiveSpan126524Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_0 : adaptiveNumericSpans126524_0.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_0 : adaptiveSpanEven126524_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_0 : adaptiveSpanEven126524_0.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_0 : adaptiveSpanEven126524_0.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_0 : adaptiveSpanWhole126524_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_0 : adaptiveSpanWhole126524_0.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_0 : adaptiveSpanWhole126524_0.spans = coreWholeSpans 0 adaptiveNumericSpans126524_0 := by
  decide +kernel
end Erdos883Verified
