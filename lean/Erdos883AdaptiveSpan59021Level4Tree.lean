import Erdos883AdaptiveSpan59021Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_4 : adaptiveNumericSpans59021_4.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_4 : adaptiveSpanEven59021_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_4 : adaptiveSpanEven59021_4.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_4 : adaptiveSpanEven59021_4.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_4 : adaptiveSpanWhole59021_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_4 : adaptiveSpanWhole59021_4.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_4 : adaptiveSpanWhole59021_4.spans = coreWholeSpans 0 adaptiveNumericSpans59021_4 := by
  decide +kernel
end Erdos883Verified
