import Erdos883AdaptiveSpan126524Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_2 : adaptiveNumericSpans126524_2.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_2 : adaptiveSpanEven126524_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_2 : adaptiveSpanEven126524_2.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_2 : adaptiveSpanEven126524_2.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_2 : adaptiveSpanWhole126524_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_2 : adaptiveSpanWhole126524_2.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_2 : adaptiveSpanWhole126524_2.spans = coreWholeSpans 0 adaptiveNumericSpans126524_2 := by
  decide +kernel
end Erdos883Verified
