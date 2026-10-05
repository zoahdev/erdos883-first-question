import Erdos883AdaptiveSpan126524Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_3 : adaptiveNumericSpans126524_3.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_3 : adaptiveSpanEven126524_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_3 : adaptiveSpanEven126524_3.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_3 : adaptiveSpanEven126524_3.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_3 : adaptiveSpanWhole126524_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_3 : adaptiveSpanWhole126524_3.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_3 : adaptiveSpanWhole126524_3.spans = coreWholeSpans 0 adaptiveNumericSpans126524_3 := by
  decide +kernel
end Erdos883Verified
