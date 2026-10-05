import Erdos883AdaptiveSpan126524Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_8 : adaptiveNumericSpans126524_8.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_8 : adaptiveSpanEven126524_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_8 : adaptiveSpanEven126524_8.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_8 : adaptiveSpanEven126524_8.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_8 : adaptiveSpanWhole126524_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_8 : adaptiveSpanWhole126524_8.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_8 : adaptiveSpanWhole126524_8.spans = coreWholeSpans 0 adaptiveNumericSpans126524_8 := by
  decide +kernel
end Erdos883Verified
