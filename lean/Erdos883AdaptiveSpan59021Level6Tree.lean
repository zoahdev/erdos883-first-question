import Erdos883AdaptiveSpan59021Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_6 : adaptiveNumericSpans59021_6.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_6 : adaptiveSpanEven59021_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_6 : adaptiveSpanEven59021_6.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_6 : adaptiveSpanEven59021_6.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_6 : adaptiveSpanWhole59021_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_6 : adaptiveSpanWhole59021_6.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_6 : adaptiveSpanWhole59021_6.spans = coreWholeSpans 0 adaptiveNumericSpans59021_6 := by
  decide +kernel
end Erdos883Verified
