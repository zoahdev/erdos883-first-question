import Erdos883AdaptiveSpan126524Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_7 : adaptiveNumericSpans126524_7.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_7 : adaptiveSpanEven126524_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_7 : adaptiveSpanEven126524_7.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_7 : adaptiveSpanEven126524_7.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_7 : adaptiveSpanWhole126524_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_7 : adaptiveSpanWhole126524_7.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_7 : adaptiveSpanWhole126524_7.spans = coreWholeSpans 0 adaptiveNumericSpans126524_7 := by
  decide +kernel
end Erdos883Verified
