import Erdos883AdaptiveSpan126524Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_4 : adaptiveNumericSpans126524_4.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_4 : adaptiveSpanEven126524_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_4 : adaptiveSpanEven126524_4.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_4 : adaptiveSpanEven126524_4.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_4 : adaptiveSpanWhole126524_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_4 : adaptiveSpanWhole126524_4.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_4 : adaptiveSpanWhole126524_4.spans = coreWholeSpans 0 adaptiveNumericSpans126524_4 := by
  decide +kernel
end Erdos883Verified
